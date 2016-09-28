import clause lpo cdcl_solver
open tactic monad expr

structure locked_cls :=
(id : name)
(c : cls)
(assertions : list expr)
(reasons : list (list expr))

namespace locked_cls

meta instance : has_to_tactic_format locked_cls :=
⟨λc, do
c_fmt ← pp c↣c,
ass_fmt ← pp (c↣assertions↣for (λa, a↣local_type)),
reasons_fmt ← pp (c↣reasons↣for (λr, r↣for (λa, a↣local_type))),
return $ c_fmt ++ " <-- " ++ ass_fmt ++ " (reasons: " ++ reasons_fmt ++ ")"
⟩

end locked_cls

structure active_cls :=
(id : name)
(selected : list nat)
(c : cls)
(assertions : list expr)
(from_model : bool)

namespace active_cls

meta instance : has_to_tactic_format active_cls :=
⟨λc, do
c_fmt ← pp c↣c,
ass_fmt ← pp (c↣assertions↣for (λa, a↣local_type)),
return $ c_fmt ++ " <-- " ++ ass_fmt ++
       " (selected: " ++ to_fmt c↣selected ++ ", model: " ++ to_fmt c↣from_model ++ ")"
⟩

meta def clause_with_assertions (ac : active_cls) : cls :=
ac↣c↣close_constn ac↣assertions

end active_cls

structure passive_cls :=
(c : cls)
(assertions : list expr)
(from_model : bool)

namespace passive_cls

meta instance : has_to_tactic_format passive_cls :=
⟨λc, pp c↣c⟩

meta def clause_with_assertions (pc : passive_cls) : cls :=
pc↣c↣close_constn pc↣assertions

end passive_cls

structure resolution_prover_state :=
(active : rb_map name active_cls)
(passive : rb_map name passive_cls)
(newly_derived : list cls)
(prec : list expr)
(locked : list locked_cls)
(sat_solver : cdcl.state)
(current_model : rb_map expr bool)
(sat_hyps : rb_map expr (expr × expr))
(needs_sat_run : bool)
(age : nat)

open resolution_prover_state

private meta def join_with_nl : list format → format :=
list.foldl (λx y, x ++ format.line ++ y) format.nil

private meta def resolution_prover_state_tactic_fmt (s : resolution_prover_state) : tactic format := do
active_fmts ← mapM pp (rb_map.values s↣active),
passive_fmts ← mapM pp (rb_map.values s↣passive),
new_fmts ← mapM pp s↣newly_derived,
locked_fmts ← mapM pp s↣locked,
sat_fmts ← mapM pp s↣sat_solver↣given,
prec_fmts ← mapM pp s↣prec,
return (join_with_nl
  ([to_fmt "active:"] ++ map (append (to_fmt "  ")) active_fmts ++
  [to_fmt "passive:"] ++ map (append (to_fmt "  ")) passive_fmts ++
  [to_fmt "new:"] ++ map (append (to_fmt "  ")) new_fmts ++
  [to_fmt "locked:"] ++ map (append (to_fmt "  ")) locked_fmts ++
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
do st ← stateT.read, if st↣sat_hyps↣contains v then return () else do
hpv ← resolution_prover_of_tactic mk_fresh_name,
hnv ← resolution_prover_of_tactic mk_fresh_name,
univ ← resolution_prover_of_tactic $ infer_univ v,
stateT.modify $ λst, { st with sat_hyps := st↣sat_hyps↣insert v
  (local_const hpv hpv binder_info.default v,
   local_const hnv hnv binder_info.default
               (if univ = level.zero then not_ v else imp v false_)) },
in_sat_solver $ cdcl.mk_var_core v suggested_ph

meta def get_sat_hyp_core (v : expr) (ph : bool) : resolution_prover (option expr) :=
flip liftM stateT.read $ λst,
  match st↣sat_hyps↣find v with
  | some (hp, hn) := some $ if ph then hp else hn
  | none := none
  end

meta def get_sat_hyp (v : expr) (ph : bool) : resolution_prover expr :=
do hyp_opt ← get_sat_hyp_core v ph,
match hyp_opt with
| some hyp := return hyp
| none := resolution_prover.fail $ "unknown sat variable: " ++ v↣to_string
end

meta def add_sat_clause (c : cls) : resolution_prover unit := do
already_added ← flip liftM stateT.read (λst, decidable.to_bool $
                     c↣type ∈ st↣sat_solver↣given↣for (λd, d↣type)),
if already_added then return () else do
forM c↣get_lits $ λl, mk_sat_var l↣formula l↣is_neg,
in_sat_solver $ cdcl.mk_clause c,
stateT.modify $ λst, { st with needs_sat_run := tt }

meta def sat_eval_lit (v : expr) (pol : bool) : resolution_prover bool :=
do v_st ← flip liftM stateT.read $ λst, st↣current_model↣find v,
match v_st with
| some ph := return $ if pol then ph else bnot ph
| none := return tt
end

meta def sat_eval_assertion (assertion : expr) : resolution_prover bool :=
match is_not assertion↣local_type with
| some v := sat_eval_lit v ff
| none := sat_eval_lit assertion↣local_type tt
end

meta def sat_eval_assertions : list expr → resolution_prover bool
| (a::ass) := do v_a ← sat_eval_assertion a,
                 if v_a then
                   sat_eval_assertions ass
                 else
                   return ff
| [] := return tt

private meta def get_new_cls_id : resolution_prover name := do
state ← stateT.read,
stateT.write { state with age := state↣age + 1 },
cls_prefix ← resolution_prover_of_tactic $ get_unused_name `cls none,
return $ mk_num_name cls_prefix state↣age

meta def collect_ass_hyps (c : cls) : resolution_prover (list expr) :=
let lcs := contained_lconsts c↣prf in
do st ← stateT.read,
return (do
  hs ← st↣sat_hyps↣values,
  h ← [hs↣1, hs↣2],
  guard $ lcs↣contains h↣local_uniq_name,
  [h])

meta def register_as_passive (c : cls) : resolution_prover unit := do
ass ← collect_ass_hyps c,
ass_v ← sat_eval_assertions ass,
if c↣num_quants = 0 ∧ c↣num_lits = 0 then
  add_sat_clause (c↣close_constn ass)
else if ¬ass_v then do
  id ← get_new_cls_id,
  stateT.modify $ λst, { st with locked := ⟨ id, c, ass, [] ⟩ :: st↣locked }
else do
  id ← get_new_cls_id,
  c' ← return $ c↣close_constn ass,
  resolution_prover_of_tactic (assertv id c'↣type c'↣prf),
  prf' ← resolution_prover_of_tactic (get_local id),
  resolution_prover_of_tactic $ infer_type prf', -- FIXME: otherwise ""
  stateT.modify $ λstate, { state with passive :=
    state↣passive↣insert id { c := { c with prf := app_of_list prf' ass },
                              assertions := ass,
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
  reason_vals ← mapM sat_eval_assertions lc↣reasons,
  c_val ← sat_eval_assertions lc↣assertions,
  if reason_vals↣for_all (λr, r = ff) ∧ c_val then do
    stateT.modify $ λst, { st with passive := st↣passive↣insert lc↣id ⟨ lc↣c, lc↣assertions, ff ⟩ },
    return ff
  else
    return tt
),
stateT.modify $ λst, { st with locked := new_locked }

meta def move_active_to_locked : resolution_prover unit :=
-- FIXME: update assertions field in remaining active clauses
do active ← get_active, forM' active↣values $ λac, do
  c_val ← sat_eval_assertions ac↣assertions,
  if ¬c_val then do
     stateT.modify $ λst, { st with
       active := st↣active↣erase ac↣id,
       locked := ⟨ ac↣id, ac↣c, ac↣assertions, [] ⟩ :: st↣locked
     }
  else
    return ()

meta def move_passive_to_locked : resolution_prover unit :=
-- FIXME: update assertions field in remaining passive clauses
do passive ← flip liftM stateT.read (λst, st↣passive), forM' passive↣to_list $ λpc, do
  c_val ← sat_eval_assertions pc↣2↣assertions,
  if ¬c_val then do
    stateT.modify $ λst, { st with
      passive := st↣passive↣erase pc↣1,
      locked := ⟨ pc↣1, pc↣2↣c, pc↣2↣assertions, [] ⟩ :: st↣locked
    }
  else
    return ()

meta def add_from_model_clauses : resolution_prover unit := do
model ← flip liftM stateT.read (λst, st↣current_model),
forM' model↣to_list $ λassg, do
  name ← resolution_prover_of_tactic mk_fresh_name,
  hyp ← get_sat_hyp assg↣1 assg↣2,
  stateT.modify $ λst, { st with
    passive := st↣passive↣insert name $
      if assg↣2 = tt then
        ⟨ ⟨ 0, 1, tt, hyp, assg↣1 ⟩, [hyp], tt ⟩
      else
        ⟨ ⟨ 0, 1, ff, hyp, imp assg↣1 false_ ⟩, [hyp], tt ⟩
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
guard $ parents↣for_all (λp, p↣id ≠ id),
red_opt ← flip liftM stateT.read (λst, st↣active↣find id),
match red_opt with
| none := return ()
| some red :=
  if red↣from_model then do
    stateT.modify $ λst, { st with active := st↣active↣erase id }
  else
  let reasons := parents↣for (λp, p↣assertions),
      assertion := red↣assertions in
  if reasons↣for_all (λr, r↣subset_of assertion) then do
    stateT.modify $ λst, { st with active := st↣active↣erase id }
  else do
    stateT.modify $ λst, { st with active := st↣active↣erase id,
                                   locked := ⟨ id, red↣c, red↣assertions, reasons ⟩ :: st↣locked }
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
  current_model := rb_map.mk _ _, sat_hyps := rb_map.mk _ _, needs_sat_run := ff }

meta def initial (clauses : list cls) : tactic resolution_prover_state := do
after_setup ← forM' clauses (λc, add_inferred c []) empty,
return after_setup.2

end resolution_prover_state
