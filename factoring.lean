import clause prover_state
open tactic expr monad

meta_definition inst_lit (c : cls) (i : nat) (e : expr) : tactic cls := do
opened ← cls.open_constn c i,
return $ cls.close_constn (cls.inst opened.1 e) opened.2

private meta_definition try_factor' (gt : expr → expr → bool) (c : cls) (i j : nat) : tactic cls := do
qf ← cls.open_metan c (cls.num_quants c),
unify_lit (cls.get_lit qf.1 i) (cls.get_lit qf.1 j),
qfi ← cls.inst_mvars qf.1,
@guard tactic _ (cls.is_maximal gt qfi i = tt) _,
at_j ← cls.open_constn qf.1 j,
hyp_i ← monadfail_of_option (list.nth at_j.2 i),
cs ← sort_and_constify_metas qf.2,
qf' ← cls.inst_mvars $
  if cls.has_fin c = tt ∧ j+1 = cls.num_lits c then
    cls.close_constn (cls.of_proof_and_type (app hyp_i (cls.prf at_j.1)) (const ``false [])) at_j.2
  else
    cls.close_constn (cls.inst at_j.1 hyp_i) at_j.2,
return $ cls.close_constn qf' cs

meta_definition try_factor (gt : expr → expr → bool) (c : cls) (i j : nat) : tactic cls :=
if i > j then try_factor' gt c j i else try_factor' gt c i j

meta_definition try_infer_factor (gt : expr → expr → bool) (c : cls) (i j : nat) : resolution_prover unit := do
f ← resolution_prover_of_tactic (try_factor gt c i j),
add_inferred f

meta_definition factor_inf : inference :=
take given, do gt ← get_term_order, sequence' (do
  i ← active_cls.selected given,
  j ← range (cls.num_lits (active_cls.c given)),
  return $ @orelse resolution_prover _ _ (try_infer_factor gt (active_cls.c given) i j) (return ())
)
