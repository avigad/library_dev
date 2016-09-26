import clause prover_state
import subsumption misc_preprocessing
import resolution factoring clausifier superposition equality
import selection
open monad tactic expr

declare_trace resolution
set_option trace.resolution false

meta def trace_clauses : resolution_prover unit := do
state ← stateT.read,
resolution_prover_of_tactic (tactic.trace state)

meta def run_prover_loop
  (literal_selection : selection_strategy)
  (clause_selection : clause_selection_strategy)
  (preprocessing_rules : list (resolution_prover unit))
  (inference_rules : list inference)
  : ℕ → resolution_prover (option expr) | i := do
sequence' preprocessing_rules,
new ← take_newly_derived, forM' new register_as_passive,
resolution_prover_of_tactic (when (is_trace_enabled_for `resolution) (forM' new (λn,
  trace { n with prf := const (mk_simple_name " derived") [] }))),
passive ← get_passive,
if rb_map.size passive = 0 then return none else do
given_name ← clause_selection i,
given ← option.to_monad (rb_map.find passive given_name),
-- trace_clauses,
remove_passive given_name,
if is_false (cls.type given) then return (some (cls.prf given)) else do
selected_lits ← literal_selection given,
activated_given ← return $ active_cls.mk given_name selected_lits given,
resolution_prover_of_tactic (when (is_trace_enabled_for `resolution) (do
  fmt ← pp activated_given, trace (to_fmt "given: " ++ fmt))),
add_active activated_given,
seq_inferences inference_rules activated_given,
run_prover_loop (i+1)

meta def default_preprocessing : list (resolution_prover unit) :=
[
remove_duplicates_pre,
refl_r_pre,
tautology_removal_pre,
subsumption_interreduction_pre,
forward_subsumption_pre,
return ()
]

meta def default_inferences : list inference :=
[
clausification_inf,
forward_subsumption, backward_subsumption,
factor_inf,
resolution_inf,
superposition_inf,
unify_eq_inf,
(λg, return ())
]

meta def prover_tactic : tactic unit := do
intros,
target_name ← get_unused_name `target none, tgt ← target,
mk_mapp ``classical.by_contradiction [some tgt] >>= apply, intro target_name,
hyps ← local_context,
initial_clauses ← mapM cls.of_proof hyps,
initial_state ← resolution_prover_state.initial initial_clauses,
res ← run_prover_loop selection21 (age_weight_clause_selection 6 7)
  default_preprocessing default_inferences
  0 initial_state,
match res with
| (some empty_clause, _) := apply empty_clause
| (none, saturation) := trace "saturation" >> trace saturation >> skip
end
