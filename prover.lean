import clause prover_state
import subsumption misc_preprocessing
import resolution factoring clausifier
open monad tactic expr

meta_definition trace_clauses : resolution_prover unit := do
@monad.bind resolution_prover _ _ _ stateT.read
(λstate, resolution_prover_of_tactic (tactic.trace state))

meta_definition run_prover_loop
  (literal_selection : selection_strategy)
  (clause_selection : resolution_prover name)
  (preprocessing_rules : list (resolution_prover unit))
  (inference_rules : list inference)
  : resolution_prover (option expr) := do
sequence' preprocessing_rules,
new ← take_newly_derived, forM' new register_as_passive,
passive : rb_map name cls ← get_passive,
if rb_map.size passive = 0 then trace_clauses >> return none else do
given_name ← clause_selection,
given ← @monadfail_of_option resolution_prover _ resolution_prover_is_alternative _ (rb_map.find passive given_name),
-- trace_clauses,
remove_passive given_name,
if is_false (cls.type given) = tt then return (some (cls.prf given)) else do
selected_lits ← literal_selection given,
activated_given ← return $ active_cls.mk given_name selected_lits given,
resolution_prover_of_tactic (do fmt ← pp activated_given, trace (to_fmt "given: " ++ fmt)),
add_active activated_given,
seq_inferences inference_rules activated_given,
run_prover_loop literal_selection clause_selection preprocessing_rules inference_rules

meta_definition default_preprocessing : list (resolution_prover unit) :=
[
tautology_removal_pre,
subsumption_interreduction_pre,
forward_subsumption_pre
]

meta_definition default_inferences : list inference :=
[
forward_subsumption, backward_subsumption,
clausification_inference,
resolution_inf, factor_inf
]

meta_definition try_clausify (prf : expr) : tactic (list cls) :=
(do c ← cls.of_proof prf, return [c]) <|> return []

meta_definition prover_tactic : tactic unit := do
intros,
target_name ← mk_fresh_name,
mk_const ``classical.by_contradiction >>= apply, intro target_name,
hyps ← local_context,
initial_clauses ← @mapM tactic _ _ _ try_clausify hyps,
res ← run_prover_loop dumb_selection weight_clause_selection
  default_preprocessing default_inferences
  (resolution_prover_state.mk (rb_map.mk name active_cls) (rb_map.mk name cls) (join initial_clauses)),
match res with
| (some empty_clause, _) := apply empty_clause
| (none, _) := trace "saturation" >> skip
end
