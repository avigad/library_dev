import clause lpo cdcl_solver
open tactic monad

structure locked_cls :=
(id : name)
(c : cls)
(reasons : list (list cls.lit))

structure active_cls :=
(id : name)
(selected : list nat)
(c : cls)
(assertions : list ℕ)
(from_model : bool)

namespace active_cls

meta instance : has_to_tactic_format active_cls :=
⟨λc, do
c_fmt ← pp c↣c,
model_fmt ← return $ if c↣from_model then "<model> " else "",
return $ to_fmt model_fmt ++ c_fmt ++ to_fmt " (selected: " ++ to_fmt (active_cls.selected c) ++ to_fmt ")"
⟩

meta def assertion_lits (ac : active_cls) : list cls.lit :=
ac↣assertions↣for $ λi, ac↣c↣get_lit i

end active_cls

structure passive_cls :=
(c : cls)
(assertions : list ℕ)
(from_model : bool)

namespace passive_cls

meta instance : has_to_tactic_format passive_cls :=
⟨λc, do
c_fmt ← pp c↣c,
model_fmt ← return $ if c↣from_model then "<model> " else "",
return $ model_fmt ++ c_fmt
⟩

end passive_cls

structure resolution_prover_state :=
(active : rb_map name active_cls)
(passive : rb_map name passive_cls)
(newly_derived : list cls)
(prec : list expr)
(locked : list locked_cls)
(sat_solver : cdcl.state)
(current_model : rb_map expr bool)
(needs_sat_run : bool)
(age : nat)

open resolution_prover_state

private meta def join_with_nl : list format → format :=
list.foldl (λx y, x ++ format.line ++ y) format.nil

private meta def resolution_prover_state_tactic_fmt (s : resolution_prover_state) : tactic format := do
active_fmts ← mapM pp (rb_map.values s↣active),
passive_fmts ← mapM pp (rb_map.values s↣passive),
new_fmts ← mapM pp s↣newly_derived,
sat_fmts ← mapM pp s↣sat_solver↣given,
prec_fmts ← mapM pp s↣prec,
return (join_with_nl
  ([to_fmt "active:"] ++ map (append (to_fmt "  ")) active_fmts ++
  [to_fmt "passive:"] ++ map (append (to_fmt "  ")) passive_fmts ++
  [to_fmt "new:"] ++ map (append (to_fmt "  ")) new_fmts ++
  [to_fmt "sat formulas:"] ++ map (append (to_fmt "  ")) sat_fmts ++
  [to_fmt "precedence order: " ++ to_fmt prec_fmts]))

meta instance : has_to_tactic_format resolution_prover_state :=
⟨resolution_prover_state_tactic_fmt⟩

meta def resolution_prover :=
stateT resolution_prover_state tactic

meta instance : monad resolution_prover := stateT.monad _ _

meta def resolution_prover_of_tactic {a} (tac : tactic a) : resolution_prover a :=
λs, do res ← tac, return (res, s)

meta def resolution_prover.fail {A B : Type} [has_to_format B] (msg : B) : resolution_prover A :=
resolution_prover_of_tactic (tactic.fail msg)

meta def resolution_prover.failed {A : Type} : resolution_prover A :=
resolution_prover.fail "failed"

meta def resolution_prover.orelse {A : Type} (p1 p2 : resolution_prover A) : resolution_prover A :=
take state, p1 state <|> p2 state

meta instance : alternative resolution_prover :=
alternative.mk (@monad.map _ _)
  (@applicative.pure _ (monad_is_applicative resolution_prover))
  (@applicative.seq _ (monad_is_applicative resolution_prover))
  @resolution_prover.failed
  @resolution_prover.orelse

meta def selection_strategy := passive_cls → resolution_prover (list nat)

meta def get_active : resolution_prover (rb_map name active_cls) :=
do state ← stateT.read, return state↣active

meta def add_active (a : active_cls) : resolution_prover unit :=
do state ← stateT.read,
stateT.write { state with active := state↣active↣insert a↣id a }

meta def get_passive : resolution_prover (rb_map name passive_cls) :=
liftM passive stateT.read

meta def in_sat_solver {A} (cmd : cdcl.solver A) : resolution_prover A := do
state ← stateT.read,
result ← resolution_prover_of_tactic $ cmd state↣sat_solver,
stateT.write { state with sat_solver := result↣2 },
return result↣1

meta def mk_sat_var (v : expr) (suggested_ph : bool) : resolution_prover unit :=
in_sat_solver $ cdcl.mk_var_core v suggested_ph

meta def add_sat_clause (c : cls) : resolution_prover unit := do
in_sat_solver $ cdcl.mk_clause c,
stateT.modify $ λst, { st with needs_sat_run := tt }

private meta def sat_eval_lit' (model : rb_map expr bool) (l : cls.lit) : option bool :=
match model↣find l↣formula with
| some val := some $ if l↣is_pos then val else bnot val
| none := none
end

meta def sat_eval_lit (l : cls.lit) : resolution_prover (option bool) :=
do st ← stateT.read, return $ sat_eval_lit' st↣current_model l

private meta def sat_eval_lits' (model : rb_map expr bool) : list cls.lit → option bool
| (l::ls) :=
  match sat_eval_lit' model l, sat_eval_lits' ls with
  | _,       some tt := some tt
  | some tt, _       := some tt
  | some ff, some ff := some ff
  | _,       _       := none
  end
| [] := some ff

meta def sat_eval_lits (ls : list cls.lit) : resolution_prover (option bool) :=
do st ← stateT.read, return $ sat_eval_lits' st↣current_model ls

meta def sat_eval_clause (c : cls) : resolution_prover (option bool) :=
sat_eval_lits c↣get_lits

private meta def get_new_cls_id : resolution_prover name := do
state ← stateT.read,
stateT.write { state with age := state↣age + 1 },
cls_prefix ← resolution_prover_of_tactic $ get_unused_name `cls none,
return $ mk_num_name cls_prefix state↣age

meta def select_assertions (c : cls) : resolution_prover (list ℕ) :=
flip filterM (list.range c↣num_lits) $
  λi, do v ← sat_eval_lit $ c↣get_lit i,
         return (decidable.to_bool $ v ≠ none)

meta def register_as_passive (c : cls) : resolution_prover unit :=
do c_v ← sat_eval_clause c, if c_v = some ff then add_sat_clause c else do
id ← get_new_cls_id,
resolution_prover_of_tactic (assertv id c↣type c↣prf),
prf' ← resolution_prover_of_tactic (get_local id),
resolution_prover_of_tactic $ infer_type prf', -- FIXME: otherwise ""
assertions ← select_assertions c,
stateT.modify $ λstate, { state with passive :=
  state↣passive↣insert id { c := { c with prf := prf' },
                            assertions := assertions,
                            from_model := ff }
}

meta def remove_passive (id : name) : resolution_prover unit :=
do state ← stateT.read, stateT.write { state with passive := state↣passive↣erase id }

meta def remove_from_model_clauses : resolution_prover unit :=
stateT.modify $ λst, { st with
  active := st↣active↣filter (λac, ¬ac↣from_model),
  passive := st↣passive↣filter (λpc, ¬pc↣from_model)
}

meta def move_locked_to_passive : resolution_prover unit := do
locked ← flip liftM stateT.read (λst, st↣locked),
new_locked ← flip filterM locked (λlc, do
  reason_vals ← mapM sat_eval_lits lc↣reasons,
  c_val ← sat_eval_clause lc↣c,
  if reason_vals↣for_all (λrv, rv = some tt) ∧ c_val ≠ some tt then do
    assertions ← select_assertions lc↣c,
    stateT.modify $ λst, { st with passive := st↣passive↣insert lc↣id ⟨ lc↣c, assertions, ff ⟩ },
    return ff
  else
    return tt
),
stateT.modify $ λst, { st with locked := new_locked }

meta def move_active_to_locked : resolution_prover unit :=
-- FIXME: update assertions field in remaining active clauses
do active ← get_active, forM' active↣values $ λac, do
  c_val ← sat_eval_clause ac↣c,
  if c_val = some ff then do
     add_sat_clause ac↣c,
     stateT.modify $ λst, { st with active := st↣active↣erase ac↣id }
  else if c_val = some tt then do
     stateT.modify $ λst, { st with
       active := st↣active↣erase ac↣id,
       locked := ⟨ ac↣id, ac↣c, [] ⟩ :: st↣locked
     }
  else
    return ()

meta def move_passive_to_locked : resolution_prover unit :=
-- FIXME: update assertions field in remaining passive clauses
do passive ← flip liftM stateT.read (λst, st↣passive), forM' passive↣to_list $ λpc, do
  c_val ← sat_eval_clause pc↣2↣c,
  if c_val = some ff then do
    add_sat_clause pc↣2↣c,
    stateT.modify $ λst, { st with passive := st↣passive↣erase pc↣1 }
  else if c_val = some tt then do
    stateT.modify $ λst, { st with
      passive := st↣passive↣erase pc↣1,
      locked := ⟨ pc↣1, pc↣2↣c, [] ⟩ :: st↣locked
    }
  else
    return ()

meta def add_from_model_clauses : resolution_prover unit := do
model ← flip liftM stateT.read (λst, st↣current_model),
forM' model↣to_list $ λassg, do
  name1 ← resolution_prover_of_tactic mk_fresh_name,
  name2 ← resolution_prover_of_tactic mk_fresh_name,
  prf ← resolution_prover_of_tactic $ mk_mapp ``id [some assg↣1],
  c ← return $ cls.mk 0 2 tt prf (assg↣1↣imp assg↣1),
  stateT.modify $ λst, { st with
    passive := (st↣passive↣insert name1 ⟨ c, [0], tt ⟩)↣insert name2 ⟨ c, [1], tt ⟩
  }

meta def do_sat_run : resolution_prover (option expr) :=
do sat_result ← in_sat_solver $ cdcl.run (return none),
stateT.modify $ λst, { st with needs_sat_run := ff },
old_model ← liftM resolution_prover_state.current_model stateT.read,
match sat_result with
| (cdcl.result.unsat prf) := return (some prf)
| (cdcl.result.sat new_model) := do
    stateT.modify $ λst, { st with current_model := new_model },
    remove_from_model_clauses,
    move_locked_to_passive,
    move_active_to_locked,
    move_passive_to_locked,
    add_from_model_clauses,
    return none
end

meta def take_newly_derived : resolution_prover (list cls) := do
state ← stateT.read,
stateT.write { state with newly_derived := [] },
return state↣newly_derived

meta def remove_redundant (id : name) (parents : list active_cls) : resolution_prover unit := do
red_opt ← flip liftM stateT.read (λst, st↣active↣find id),
match red_opt with
| none := return ()
| some red :=
  let reasons := parents↣for (λp, p↣assertion_lits),
      assertion := red↣assertion_lits in
  if reasons↣for_all (λr, ¬ r↣subset_of assertion) then do
    stateT.modify $ λst, { st with active := st↣active↣erase id,
                                   locked := ⟨ id, red↣c, reasons ⟩ :: st↣locked }
  else do
    resolution_prover_of_tactic $ get_local id >>= clear,
    stateT.modify $ λst, { st with active := st↣active↣erase id }
end

meta def get_precedence : resolution_prover (list expr) :=
do state ← stateT.read, return state↣prec

meta def get_term_order : resolution_prover (expr → expr → bool) := do
state ← stateT.read,
return $ lpo (prec_gt_of_name_list (map name_of_funsym state↣prec))

private meta def set_precedence (new_prec : list expr) : resolution_prover unit :=
do state ← stateT.read, stateT.write { state with prec := new_prec }

meta def register_consts_in_precedence (consts : list expr) := do
p ← get_precedence,
p_set ← return (rb_map.set_of_list (map name_of_funsym p)),
new_syms ← return $ list.filter (λc, ¬p_set↣contains (name_of_funsym c)) consts,
set_precedence (new_syms ++ p)

meta def add_inferred (c : cls) (parents : list active_cls) : resolution_prover unit := do
c' ← resolution_prover_of_tactic c↣normalize,
register_consts_in_precedence (contained_funsyms c'↣type)↣values,
state ← stateT.read,
stateT.write { state with newly_derived := c' :: state↣newly_derived }

meta def inference :=
active_cls → resolution_prover unit

meta def seq_inferences : list inference → inference
| [] := λgiven, return ()
| (inf::infs) := λgiven, do
    inf given,
    now_active ← get_active,
    if rb_map.contains now_active given↣id then
      seq_inferences infs given
    else
      return ()

meta def simp_inference (simpl : active_cls → resolution_prover (option cls)) : inference :=
λgiven, do maybe_simpld ← simpl given,
match maybe_simpld with
| some simpld := do add_inferred simpld [given], remove_redundant given↣id []
| none := return ()
end

meta def preprocessing_rule (f : list cls → resolution_prover (list cls)) : resolution_prover unit := do
state ← stateT.read,
newly_derived' ← f state↣newly_derived,
state' ← stateT.read,
stateT.write { state' with newly_derived := newly_derived' }

meta def clause_selection_strategy := ℕ → resolution_prover name

namespace resolution_prover_state

meta def empty : resolution_prover_state :=
{ active := rb_map.mk _ _, passive := rb_map.mk _ _,
  newly_derived := [], prec := [], age := 0,
  locked := [], sat_solver := cdcl.state.initial,
  current_model := rb_map.mk _ _, needs_sat_run := ff }

meta def initial (clauses : list cls) : tactic resolution_prover_state := do
after_setup ← forM' clauses (λc, add_inferred c []) empty,
return after_setup.2

end resolution_prover_state
