import clause prover_state utils
open tactic monad

variable gt : expr → expr → bool
variables (ac1 ac2 : active_cls)
variables (c1 c2 : clause)
variables (i1 i2 : nat)

-- c1 : ... → a
-- c2 : ... → a → ...
meta def try_resolve : tactic clause := do
qf1 ← clause.open_metan c1 c1↣num_quants,
qf2 ← clause.open_metan c2 c2↣num_quants,
unify (clause.literal.formula (clause.get_lit qf1.1 i1)) (clause.literal.formula (clause.get_lit qf2.1 i2)),
qf1i ← clause.inst_mvars qf1.1,
guard $ clause.is_maximal gt qf1i i1,
focused_qf1 ← clause.focus qf1.1 i1,
op1 ← clause.open_constn focused_qf1 focused_qf1↣num_binders,
op2 ← clause.open_constn qf2.1 i2,
clause.meta_closure (qf1.2 ++ qf2.2) $
  clause.close_constn (clause.inst op2.1 op1↣1↣prf) (op1.2 ++ op2.2)

meta def try_add_resolvent : resolution_prover unit := do
c' ← resolution_prover_of_tactic $ try_resolve gt ac1↣c ac2↣c i1 i2,
add_inferred c' [ac1, ac2]

meta def maybe_add_resolvent : resolution_prover unit :=
try_add_resolvent gt ac1 ac2 i1 i2 <|> return ()

meta def resolution_left_inf : inference :=
take given, do active : rb_map name active_cls ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_neg (given↣c↣get_lit given_i),
  other ← rb_map.values active,
  other_i ← other↣selected,
  guard $ clause.literal.is_pos (other↣c↣get_lit other_i),
  [maybe_add_resolvent gt other given other_i given_i]

meta def resolution_right_inf : inference :=
take given, do active : rb_map name active_cls ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_pos (given↣c↣get_lit given_i),
  other ← rb_map.values active,
  other_i ← other↣selected,
  guard $ clause.literal.is_neg (other↣c↣get_lit other_i),
  [maybe_add_resolvent gt given other given_i other_i]

meta def resolution_inf : inference :=
take given, do gt ← get_term_order, resolution_left_inf gt given >> resolution_right_inf gt given
