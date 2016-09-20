import clause prover_state
open expr list

meta_definition is_taut (c : cls) : bool := do
list_orb (do
  l1 ← cls.get_lits c, guard $ cls.lit.is_neg l1 = tt,
  l2 ← cls.get_lits c, guard $ cls.lit.is_pos l2 = tt,
  [alpha_eqv (cls.lit.formula l1) (cls.lit.formula l2)])

meta_definition tautology_removal_pre : resolution_prover unit :=
preprocessing_rule $ λnew, return (filter (λc, bool.bnot (is_taut c)) new)
