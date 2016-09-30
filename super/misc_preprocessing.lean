import clause prover_state
open expr list monad

meta def is_taut (c : clause) : tactic bool := do
qf ← clause.open_constn c c↣num_quants,
return $ list.bor (do
  l1 ← clause.get_lits qf.1, guard $ clause.literal.is_neg l1,
  l2 ← clause.get_lits qf.1, guard $ clause.literal.is_pos l2,
  [decidable.to_bool (clause.literal.formula l1 = clause.literal.formula l2)])

open tactic
example (i : Type) (p : i → i → Type) (c : i) (h : ∀ (x : i), p x c → p x c) : true := by do
h ← get_local `h, hcls ← clause.of_proof h,
taut ← is_taut hcls,
when (¬taut) failed,
to_expr `(trivial) >>= apply

meta def tautology_removal_pre : resolution_prover unit :=
preprocessing_rule $ λnew, filterM (λc, liftM bnot ↑(is_taut c)) new

meta def remove_duplicates_pre : resolution_prover unit :=
preprocessing_rule $ λnew,
return (rb_map.values (rb_map.of_list (list.map (λc:clause, (c↣type, c)) new)))
