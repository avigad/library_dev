import clause prover_state
open tactic expr monad

meta_definition inst_lit (c : cls) (i : nat) (e : expr) : tactic cls := do
opened ← cls.open_constn c i,
return $ cls.close_constn (cls.inst opened.1 e) opened.2

meta_definition try_factor (c : cls) (i j : nat) : tactic cls :=
if i > j then try_factor c j i else do
qf ← cls.open_metan c (cls.num_quants c),
trace (cls.type qf.1),
unify_lit (cls.get_lit qf.1 i) (cls.get_lit qf.1 j),
at_j ← cls.open_constn qf.1 j,
match list.nth at_j.2 i with
| none := failed
| some hyp_i := do
  cs ← sort_and_constify_metas qf.2,
  qf' ← cls.inst_mvars $ cls.close_constn (cls.inst at_j.1 hyp_i) at_j.2,
  trace (cls.prf qf'),
  trace (cls.type qf'),
  trace cs,
  return $ cls.close_constn qf' cs
end

set_option new_elaborator true
example (i : Type) (p : i → i → Prop) (f g : i → i)
  (cls : ∀x y z w, p x (f y) → p (g z) w → false) : true :=
by do
  prf ← get_local `cls,
  type ← infer_type prf,
  c ← return $ cls.mk 4 2 prf type,
  c' ← try_factor c 0 1,
  trace (cls.prf c'),
  trace (cls.type c'),
  mk_const ``true.intro >>= apply
set_option new_elaborator false

meta_definition try_infer_factor (c : cls) (i j : nat) : resolution_prover unit := do
f ← resolution_prover_of_tactic (try_factor c i j),
add_inferred f

meta_definition factor : inference :=
take given, @sequence resolution_prover _ _ (do
  i ← active_cls.selected given,
  j ← range (cls.num_lits (active_cls.c given)),
  return $ @orelse resolution_prover _ _ (try_infer_factor (active_cls.c given) i j) (return ())
) >> return ()
