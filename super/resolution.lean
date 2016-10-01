import .clause .prover_state .utils
open tactic monad

variable gt : expr → expr → bool
variables (ac1 ac2 : active_cls)
variables (c1 c2 : clause)
variables (i1 i2 : nat)

-- c1 : ... → ¬a → ...
-- c2 : ... →  a → ...
meta def try_resolve : tactic clause := do
qf1 ← c1↣open_metan c1↣num_quants,
qf2 ← c2↣open_metan c2↣num_quants,
unify (qf1↣1↣get_lit i1)↣formula (qf2↣1↣get_lit i2)↣formula,
qf1i ← qf1↣1↣inst_mvars,
guard $ clause.is_maximal gt qf1i i1,
op1 ← qf1↣1↣open_constn i1,
op2 ← qf2↣1↣open_constn c2↣num_lits,
a_in_op2 ← (op2↣2↣nth i2)↣to_monad,
clause.meta_closure (qf1.2 ++ qf2.2) $
  (op1↣1↣inst (op2↣1↣close_const a_in_op2)↣proof)↣close_constn (op1↣2 ++ op2↣2↣remove i2)

meta def try_add_resolvent : resolution_prover unit := do
c' ← ↑(try_resolve gt ac1↣c ac2↣c i1 i2),
add_inferred c' [ac1, ac2]

meta def maybe_add_resolvent : resolution_prover unit :=
try_add_resolvent gt ac1 ac2 i1 i2 <|> return ()

meta def resolution_left_inf : inference :=
take given, do active : rb_map name active_cls ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_neg (given↣c↣get_lit given_i),
  other ← rb_map.values active,
  guard $ ¬given↣in_sos ∨ ¬other↣in_sos,
  other_i ← other↣selected,
  guard $ clause.literal.is_pos (other↣c↣get_lit other_i),
  [maybe_add_resolvent gt other given other_i given_i]

meta def resolution_right_inf : inference :=
take given, do active : rb_map name active_cls ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_pos (given↣c↣get_lit given_i),
  other ← rb_map.values active,
  guard $ ¬given↣in_sos ∨ ¬other↣in_sos,
  other_i ← other↣selected,
  guard $ clause.literal.is_neg (other↣c↣get_lit other_i),
  [maybe_add_resolvent gt given other given_i other_i]

meta def resolution_inf : inference :=
take given, do gt ← get_term_order, resolution_left_inf gt given >> resolution_right_inf gt given
