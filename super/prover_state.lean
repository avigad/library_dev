import .clause .lpo .cdcl_solver
open tactic monad expr

namespace super

meta structure locked_cls :=
(id : name)
(c : clause)
(assertions : list expr)
(reasons : list (list expr))
(in_sos : bool)

namespace locked_cls

meta instance : has_to_tactic_format locked_cls :=
⟨λc, do
c_fmt ← pp c↣c,
ass_fmt ← pp (c↣assertions↣for (λa, a↣local_type)),
reasons_fmt ← pp (c↣reasons↣for (λr, r↣for (λa, a↣local_type))),
return $ c_fmt ++ " <-- " ++ ass_fmt ++ " (reasons: " ++ reasons_fmt ++ ")"
⟩

end locked_cls

meta structure active_cls :=
(id : name)
(selected : list nat)
(c : clause)
(assertions : list expr)
(from_model : bool)
(in_sos : bool)

namespace active_cls

meta instance : has_to_tactic_format active_cls :=
⟨λc, do
c_fmt ← pp c↣c,
ass_fmt ← pp (c↣assertions↣for (λa, a↣local_type)),
return $ c_fmt ++ " <-- " ++ ass_fmt ++
       " (selected: " ++ to_fmt c↣selected ++
       ", model: " ++ to_fmt c↣from_model ++
       ", sos: " ++ to_fmt c↣in_sos ++ ")"
⟩

meta def clause_with_assertions (ac : active_cls) : clause :=
ac↣c↣close_constn ac↣assertions

end active_cls

meta structure passive_cls :=
(c : clause)
(assertions : list expr)
(from_model : bool)
(in_sos : bool)

namespace passive_cls

meta instance : has_to_tactic_format passive_cls :=
⟨λc, pp c↣c⟩

meta def clause_with_assertions (pc : passive_cls) : clause :=
pc↣c↣close_constn pc↣assertions

end passive_cls

meta structure resolution_prover_state :=
(active : rb_map name active_cls)
(passive : rb_map name passive_cls)
(newly_derived : list clause)
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
active_fmts ← mapM pp $ rb_map.values s↣active,
passive_fmts ← mapM pp $ rb_map.values s↣passive,
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

meta instance : has_coe_fam tactic resolution_prover :=
⟨λa, resolution_prover_of_tactic⟩

meta def resolution_prover.fail {A B : Type} [has_to_format B] (msg : B) : resolution_prover A :=
@tactic.fail A _ _ msg

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
result : A × cdcl.state ← ↑(cmd state↣sat_solver),
stateT.write { state with sat_solver := result↣2 },
return result↣1

meta def mk_sat_var (v : expr) (suggested_ph : bool) : resolution_prover unit :=
do st ← stateT.read, if st↣sat_hyps↣contains v then return () else do
hpv ← ↑mk_fresh_name, hnv ← ↑mk_fresh_name,
univ ← ↑(infer_univ v),
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

meta def add_sat_clause (c : clause) : resolution_prover unit := do
already_added ← flip liftM stateT.read $ λst, decidable.to_bool $
                     c↣type ∈ st↣sat_solver↣given↣for (λd, d↣type),
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
cls_prefix ← ↑(get_unused_name `clause none),
return $ mk_num_name cls_prefix state↣age

meta def collect_ass_hyps (c : clause) : resolution_prover (list expr) :=
let lcs := contained_lconsts c↣proof in
do st ← stateT.read,
return (do
  hs ← st↣sat_hyps↣values,
  h ← [hs↣1, hs↣2],
  guard $ lcs↣contains h↣local_uniq_name,
  [h])

meta def register_as_passive (c : clause) : resolution_prover unit := do
ass ← collect_ass_hyps c,
ass_v ← sat_eval_assertions ass,
id ← get_new_cls_id,
c' ← return $ c↣close_constn ass,
@coe _ (resolution_prover unit) _ (assertv id c'↣type c'↣proof),
proof' ← ↑(get_local id),
type : expr ← ↑(infer_type proof'), -- FIXME: otherwise ""
c'' ← return { c with proof := app_of_list proof' ass },
in_sos ← return $ decidable.to_bool ((contained_lconsts c↣proof)↣size = 0),
if c↣num_quants = 0 ∧ c↣num_lits = 0 then
  add_sat_clause { c' with proof := proof' }
else if ¬ass_v then do
  stateT.modify $ λst, { st with locked := ⟨ id, c'', ass, [], in_sos ⟩ :: st↣locked }
else do
  stateT.modify $ λstate, { state with passive :=
    state↣passive↣insert id { c := c'', assertions := ass, from_model := ff, in_sos := in_sos }
  }

meta def remove_passive (id : name) : resolution_prover unit :=
do state ← stateT.read, stateT.write { state with passive := state↣passive↣erase id }

meta def move_locked_to_passive : resolution_prover unit := do
locked ← flip liftM stateT.read (λst, st↣locked),
new_locked ← flip filterM locked (λlc, do
  reason_vals ← mapM sat_eval_assertions lc↣reasons,
  c_val ← sat_eval_assertions lc↣assertions,
  if reason_vals↣for_all (λr, r = ff) ∧ c_val then do
    stateT.modify $ λst, { st with passive := st↣passive↣insert lc↣id ⟨ lc↣c, lc↣assertions, ff, lc↣in_sos ⟩ },
    return ff
  else
    return tt
),
stateT.modify $ λst, { st with locked := new_locked }

meta def move_active_to_locked : resolution_prover unit :=
do active ← get_active, forM' active↣values $ λac, do
  c_val ← sat_eval_assertions ac↣assertions,
  if ¬c_val ∧ ac↣from_model then do
     stateT.modify $ λst, { st with active := st↣active↣erase ac↣id }
  else if ¬c_val ∧ ¬ac↣from_model then do
     stateT.modify $ λst, { st with
       active := st↣active↣erase ac↣id,
       locked := ⟨ ac↣id, ac↣c, ac↣assertions, [], ac↣in_sos ⟩ :: st↣locked
     }
  else
    return ()

meta def move_passive_to_locked : resolution_prover unit :=
do passive ← flip liftM stateT.read $ λst, st↣passive, forM' passive↣to_list $ λpc, do
  c_val ← sat_eval_assertions pc↣2↣assertions,
  if ¬c_val ∧ pc↣2↣from_model then do
     stateT.modify $ λst, { st with passive := st↣passive↣erase pc↣1 }
  else if ¬c_val ∧ ¬pc↣2↣from_model then do
    stateT.modify $ λst, { st with
      passive := st↣passive↣erase pc↣1,
      locked := ⟨ pc↣1, pc↣2↣c, pc↣2↣assertions, [], pc↣2↣in_sos ⟩ :: st↣locked
    }
  else
    return ()

meta def add_new_from_model_clauses (old_model : rb_map expr bool) : resolution_prover unit := do
model ← flip liftM stateT.read (λst, st↣current_model),
forM' model↣to_list $ λassg, do
  name ← ↑mk_fresh_name,
  hyp ← get_sat_hyp assg↣1 assg↣2,
  if old_model↣find assg↣1 = some assg↣2 then return () else do
  c ← ↑(clause.of_proof hyp),
  stateT.modify $ λst, { st with passive := st↣passive↣insert name ⟨ c, [hyp], tt, ff ⟩ }

meta def do_sat_run : resolution_prover (option expr) :=
do sat_result ← in_sat_solver $ cdcl.run (return none),
stateT.modify $ λst, { st with needs_sat_run := ff },
old_model ← liftM resolution_prover_state.current_model stateT.read,
match sat_result with
| (cdcl.result.unsat proof) := return (some proof)
| (cdcl.result.sat new_model) := do
    stateT.modify $ λst, { st with current_model := new_model },
    move_locked_to_passive,
    move_active_to_locked,
    move_passive_to_locked,
    add_new_from_model_clauses old_model,
    return none
end

meta def take_newly_derived : resolution_prover (list clause) := do
state ← stateT.read,
stateT.write { state with newly_derived := [] },
return state↣newly_derived

meta def remove_redundant (id : name) (parents : list active_cls) : resolution_prover unit := do
guard $ parents↣for_all $ λp, p↣id ≠ id,
red_opt ← flip liftM stateT.read (λst, st↣active↣find id),
match red_opt with
| none := return ()
| some red :=
  if red↣from_model then do
    stateT.modify $ λst, { st with active := st↣active↣erase id }
  else
  let reasons := parents↣for (λp, p↣assertions),
      assertion := red↣assertions in
  if reasons↣for_all $ λr, r↣subset_of assertion then do
    stateT.modify $ λst, { st with active := st↣active↣erase id }
  else do
    stateT.modify $ λst, { st with active := st↣active↣erase id,
                                   locked := ⟨ id, red↣c, red↣assertions, reasons, red↣in_sos ⟩ :: st↣locked }
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

meta def add_inferred (c : clause) (parents : list active_cls) : resolution_prover unit := do
c' : clause ← ↑c↣normalize,
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

meta def simp_inference (simpl : active_cls → resolution_prover (option clause)) : inference :=
λgiven, do maybe_simpld ← simpl given,
match maybe_simpld with
| some simpld := do add_inferred simpld [given], remove_redundant given↣id []
| none := return ()
end

meta def preprocessing_rule (f : list clause → resolution_prover (list clause)) : resolution_prover unit := do
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

meta def initial (clauses : list clause) : tactic resolution_prover_state := do
after_setup ← forM' clauses (λc, add_inferred c []) empty,
return after_setup.2

end resolution_prover_state

meta def inf_if_successful (parent : active_cls) (tac : tactic (list clause)) : resolution_prover unit :=
(do inferred ← ↑tac, forM' inferred $ λc, add_inferred c [parent])
<|> return ()

meta def simp_if_successful (parent : active_cls) (tac : tactic (list clause)) : resolution_prover unit :=
(do inferred ← ↑tac, forM' inferred $ λc, add_inferred c [parent], remove_redundant parent↣id [])
<|> return ()

end super
