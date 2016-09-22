import clause prover_state utils
open tactic monad expr list

meta_definition try_unify_eq_l (c : cls) (i : nat) : tactic cls := do
guard $ cls.lit.is_neg (cls.get_lit c i),
qf ← cls.open_metan c c↣num_quants,
match is_eq (cls.lit.formula (cls.get_lit qf↣1 i)) with
| none := failed
| some (lhs, rhs) := do
unify lhs rhs,
ty ← infer_type lhs,
univ ← mk_meta_univ,
refl ← return $ app_of_list (const ``eq.refl [univ]) [ty, lhs],
opened ← cls.open_constn qf↣1 i,
cls.meta_closure qf↣2 $ cls.close_constn (cls.inst opened↣1 refl) opened↣2
end

meta_definition unify_eq_inf : inference := take given, sequence' $ do
i ← given↣selected,
[(do u ← resolution_prover_of_tactic $ try_unify_eq_l given↣c i, add_inferred u) <|> return ()]

meta_definition has_refl_r (c : cls) : bool :=
list.bor $ do
lit ← cls.get_lits c,
guard $ cls.lit.is_pos lit,
match is_eq (cls.lit.formula lit) with
| some (lhs, rhs) := [decidable.to_bool (lhs = rhs)]
| none := []
end

meta_definition refl_r_pre : resolution_prover unit :=
preprocessing_rule $ take new, return (filter (λc, ¬has_refl_r c) new)
