import .clause_ops .prover_state
open tactic monad

meta def prove_using_assumption : tactic unit := do
tgt ← target,
ass ← mk_local_def `h tgt,
exact ass

meta def simplify_capturing_assumptions (type : expr) : tactic (expr × expr × list expr) := do
(type', heq) ← simplify prove_using_assumption [] type,
hyps ← return $ contained_lconsts type,
hyps' ← return $ contained_lconsts_list [type', heq],
add_hyps ← return $ list.filter (λn : expr, ¬hyps↣contains n↣local_uniq_name) hyps'↣values,
return (type', heq, add_hyps)

meta def try_simplify_left (c : clause) (i : ℕ) : tactic (list clause) :=
on_left_at c i $ λtype, do
  (type', heq, add_hyps) ← simplify_capturing_assumptions type,
  hyp ← mk_local_def `h type',
  prf  ← mk_app ``eq.mpr [heq, hyp],
  return [(hyp::add_hyps, prf)]

meta def try_simplify_right (c : clause) (i : ℕ) : tactic (list clause) :=
on_right_at' c i $ λhyp, do
  (type', heq, add_hyps) ← simplify_capturing_assumptions hyp↣local_type,
  heqtype ← infer_type heq,
  heqsymm ← mk_app ``eq.symm [heq],
  prf  ← mk_app ``eq.mpr [heqsymm, hyp],
  return [(add_hyps, prf)]

meta def inf_if_successful (parent : active_cls) (tac : tactic (list clause)) : resolution_prover unit :=
(do inferred ← ↑tac, forM' inferred $ λc, add_inferred c [parent])
<|> return ()

meta def simp_inf : inference := take given, sequence' $ do
r ← [try_simplify_right, try_simplify_left],
i ← list.range given↣c↣num_lits,
[inf_if_successful given (r given↣c i)]
