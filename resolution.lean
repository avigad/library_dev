import clause prover_state utils
open tactic monad

variable gt : expr → expr → bool
variable c1 : cls
variable c2 : cls
variable i1 : nat
variable i2 : nat

-- c1 : ... → a
-- c2 : ... → a → ...
meta_definition try_resolve : tactic cls := do
qf1 ← cls.open_metan c1 (cls.num_quants c1),
qf2 ← cls.open_metan c2 (cls.num_quants c2),
unify (cls.lit.formula (cls.get_lit qf1.1 i1)) (cls.lit.formula (cls.get_lit qf2.1 i2)),
qf1i ← cls.inst_mvars qf1.1,
guard $ cls.is_maximal gt qf1i i1,
focused_qf1 ← cls.focus qf1.1 i1,
op1 ← cls.open_constn focused_qf1 (cls.num_binders focused_qf1),
op2 ← cls.open_constn qf2.1 i2,
bs ← sort_and_constify_metas (qf1.2 ++ qf2.2),
qf' ← cls.inst_mvars $ cls.close_constn (cls.inst op2.1 (cls.prf op1.1)) (op1.2 ++ op2.2),
cls.inst_mvars $ cls.close_constn qf' bs

meta_definition try_add_resolvent : resolution_prover unit := do
c' ← resolution_prover_of_tactic $ try_resolve gt c1 c2 i1 i2,
add_inferred c'

meta_definition maybe_add_resolvent : resolution_prover unit :=
try_add_resolvent gt c1 c2 i1 i2 <|> return ()

meta_definition resolution_left_inf : inference :=
take given, do active : rb_map name active_cls ← get_active, sequence' $ do
  given_i ← active_cls.selected given,
  guard $ cls.lit.is_neg (cls.get_lit (active_cls.c given) given_i),
  other ← rb_map.values active,
  other_i ← active_cls.selected other,
  guard $ cls.lit.is_pos (cls.get_lit (active_cls.c other) other_i),
  [maybe_add_resolvent gt (active_cls.c other) (active_cls.c given) other_i given_i]

meta_definition resolution_right_inf : inference :=
take given, do active : rb_map name active_cls ← get_active, sequence' $ do
  given_i ← active_cls.selected given,
  guard $ cls.lit.is_pos (cls.get_lit (active_cls.c given) given_i),
  other ← rb_map.values active,
  other_i ← active_cls.selected other,
  guard $ cls.lit.is_neg (cls.get_lit (active_cls.c other) other_i),
  [maybe_add_resolvent gt (active_cls.c given) (active_cls.c other) given_i other_i]

meta_definition resolution_inf : inference :=
take given, do gt ← get_term_order, resolution_left_inf gt given >> resolution_right_inf gt given
