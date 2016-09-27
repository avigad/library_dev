import clause prover_state utils
open tactic monad expr list

meta def try_unify_eq_l (c : cls) (i : nat) : tactic cls := do
guard $ cls.lit.is_neg (cls.get_lit c i),
qf ← cls.open_metan c c↣num_quants,
match is_eq (qf↣1↣get_lit i)↣formula with
| none := failed
| some (lhs, rhs) := do
unify lhs rhs,
ty ← infer_type lhs,
univ ← infer_univ ty,
refl ← return $ app_of_list (const ``eq.refl [univ]) [ty, lhs],
opened ← cls.open_constn qf↣1 i,
cls.meta_closure qf↣2 $ cls.close_constn (opened↣1↣inst refl) opened↣2
end

meta def unify_eq_inf : inference := take given, sequence' $ do
i ← given↣selected,
[(do u ← resolution_prover_of_tactic $ try_unify_eq_l given↣c i, add_inferred u [given]) <|> return ()]

meta def has_refl_r (c : cls) : bool :=
list.bor $ do
lit ← c↣get_lits,
guard lit↣is_pos,
match is_eq lit↣formula with
| some (lhs, rhs) := [decidable.to_bool (lhs = rhs)]
| none := []
end

meta def refl_r_pre : resolution_prover unit :=
preprocessing_rule $ take new, return (filter (λc, ¬has_refl_r c) new)
