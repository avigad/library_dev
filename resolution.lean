import clause prover_state utils
open tactic monad

-- set_option new_elaborator true
-- c1 : ... ¬a ...
-- c2 : ...  a ...
meta_definition try_resolve (gt : expr → expr → bool) (c1 c2 : cls) (i1 i2 : nat) : tactic cls := do
qf1 ← cls.open_metan c1 (cls.num_quants c1),
qf2 ← cls.open_metan c2 (cls.num_quants c2),
unify (cls.lit.formula (cls.get_lit qf1.1 i1)) (cls.lit.formula (cls.get_lit qf2.1 i2)),
qf1i ← cls.inst_mvars qf1.1,
@guard tactic _ (cls.is_maximal gt qf1i i1 = tt) _,
op2 ← cls.open_constn qf2.1 (cls.num_lits qf2.1),
op1 ← cls.open_constn qf1.1 i1,
a_in_c2 ← monadfail_of_option (list.nth op2.2 i2),
c1_wo_not_a ← return $ cls.inst op1.1 (cls.prf (cls.close_constn op2.1 [a_in_c2])),
bs ← sort_and_constify_metas (qf1.2 ++ qf2.2),
qf' ← cls.inst_mvars $ cls.close_constn c1_wo_not_a (list_remove op2.2 i2 ++ op1.2),
cls.inst_mvars $ cls.close_constn qf' bs

meta_definition try_add_resolvent (c1 c2 : cls) (i1 i2 : nat) : resolution_prover unit := do
gt ← get_term_order,
c' ← resolution_prover_of_tactic $ try_resolve gt c1 c2 i1 i2,
add_inferred c'

meta_definition maybe_add_resolvent (c1 c2 : cls) (i1 i2 : nat) : resolution_prover unit :=
@orelse resolution_prover _ _ (try_add_resolvent c1 c2 i1 i2) (return ())

set_option new_elaborator true

meta_definition resolution_left_inf : inference :=
take given, do active : rb_map name active_cls ← get_active, sequence' $ do
  given_i ← active_cls.selected given,
  guard $ cls.lit.is_neg (cls.get_lit (active_cls.c given) given_i) = tt,
  other ← rb_map.values active,
  other_i ← active_cls.selected other,
  guard $ cls.lit.is_pos (cls.get_lit (active_cls.c other) other_i) = tt,
  [maybe_add_resolvent (active_cls.c other) (active_cls.c given) other_i given_i]

meta_definition resolution_right_inf : inference :=
take given, do active : rb_map name active_cls ← get_active, sequence' $ do
  given_i ← active_cls.selected given,
  guard $ cls.lit.is_pos (cls.get_lit (active_cls.c given) given_i) = tt,
  other ← rb_map.values active,
  other_i ← active_cls.selected other,
  guard $ cls.lit.is_neg (cls.get_lit (active_cls.c other) other_i) = tt,
  [maybe_add_resolvent (active_cls.c given) (active_cls.c other) given_i other_i]

meta_definition resolution_inf : inference :=
take given, resolution_left_inf given >> resolution_right_inf given
