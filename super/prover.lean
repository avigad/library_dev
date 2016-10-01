import .clause .prover_state
import .subsumption .misc_preprocessing
import .resolution .factoring .clausifier .superposition .equality .splitting
import .inhabited
import .selection
open monad tactic expr

declare_trace resolution
set_option trace.resolution false

meta def trace_clauses : resolution_prover unit := do
state ← stateT.read,
↑(trace state)

meta def run_prover_loop
  (literal_selection : selection_strategy)
  (clause_selection : clause_selection_strategy)
  (preprocessing_rules : list (resolution_prover unit))
  (inference_rules : list inference)
  : ℕ → resolution_prover (option expr) | i := do
sequence' preprocessing_rules,
new ← take_newly_derived, forM' new register_as_passive,
() : unit ← ↑(when (is_trace_enabled_for `resolution) (forM' new (λn,
  trace { n with proof := const (mk_simple_name " derived") [] }))),
needs_sat_run ← flip liftM stateT.read (λst, st↣needs_sat_run),
if needs_sat_run then do
  res ← do_sat_run,
  match res with
  | some proof := return (some proof)
  | none := do
    model ← flip liftM stateT.read (λst, st↣current_model),
    () : unit ← ↑(when (is_trace_enabled_for `resolution) $ do
      pp_model ← pp (model↣to_list↣for (λlit, if lit↣2 = tt then lit↣1 else not_ lit↣1)),
      trace $ to_fmt "sat model: " ++ pp_model),
    run_prover_loop i
  end
else do
passive ← get_passive,
if rb_map.size passive = 0 then return none else do
given_name ← clause_selection i,
given ← option.to_monad (rb_map.find passive given_name),
-- trace_clauses,
remove_passive given_name,
selected_lits ← literal_selection given,
activated_given ← return $ active_cls.mk given_name selected_lits given↣c given↣assertions given↣from_model given↣in_sos,
() : unit ← ↑(when (is_trace_enabled_for `resolution) (do
  fmt ← pp activated_given, trace (to_fmt "given: " ++ fmt))),
add_active activated_given,
seq_inferences inference_rules activated_given,
run_prover_loop (i+1)

meta def default_preprocessing : list (resolution_prover unit) :=
[
factor_dup_lits_pre,
remove_duplicates_pre,
refl_r_pre,
tautology_removal_pre,
subsumption_interreduction_pre,
forward_subsumption_pre,
splitting_pre,
return ()
]

meta def default_inferences : list inference :=
[
clausification_inf,
inhabited_infs,
forward_subsumption, backward_subsumption,
splitting_inf,
factor_inf,
resolution_inf,
superposition_inf,
unify_eq_inf,
(λg, return ())
]

meta def super (sos_lemmas : list expr) : tactic unit := do
intros,
target_name ← get_unused_name `target none, tgt ← target,
mk_mapp ``classical.by_contradiction [some tgt] >>= apply, intro target_name,
hyps ← local_context,
initial_clauses ← mapM clause.of_proof (hyps ++ sos_lemmas),
initial_state ← resolution_prover_state.initial initial_clauses,
res ← run_prover_loop selection21 (age_weight_clause_selection 6 7)
  default_preprocessing default_inferences
  0 initial_state,
match res with
| (some empty_clause, st) := apply empty_clause
| (none, saturation) := do sat_fmt ← pp saturation,
                           fail $ to_fmt "saturation:" ++ format.line ++ sat_fmt
end

namespace tactic.interactive

meta def with_lemmas (ls : types.raw_ident_list) : tactic unit := monad.forM' ls $ λl, do
p ← mk_const l,
t ← infer_type p,
n ← get_unused_name p↣get_app_fn↣const_name none,
tactic.assertv n t p

meta def super (extra_lemma_names : types.with_ident_list) : tactic unit := do
extra_lemmas ← mapM mk_const extra_lemma_names,
super extra_lemmas

end tactic.interactive
