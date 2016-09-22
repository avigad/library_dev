import clause prover_state subsumption
open tactic expr monad

variable gt : expr → expr → bool

meta_definition inst_lit (c : cls) (i : nat) (e : expr) : tactic cls := do
opened ← cls.open_constn c i,
return $ cls.close_constn (cls.inst opened.1 e) opened.2

private meta_definition try_factor' (c : cls) (i j : nat) : tactic cls := do
qf ← cls.open_metan c (cls.num_quants c),
unify_lit (cls.get_lit qf.1 i) (cls.get_lit qf.1 j),
qfi ← cls.inst_mvars qf.1,
guard $ cls.is_maximal gt qfi i,
at_j ← cls.open_constn qf.1 j,
hyp_i ← option.to_monad (list.nth at_j.2 i),
cs ← sort_and_constify_metas qf.2,
qf' ← cls.inst_mvars $
  if cls.has_fin c ∧ j+1 = cls.num_lits c then
    cls.close_constn (cls.of_proof_and_type (app hyp_i (cls.prf at_j.1)) (const ``false [])) at_j.2
  else
    cls.close_constn (cls.inst at_j.1 hyp_i) at_j.2,
return $ cls.close_constn qf' cs

meta_definition try_factor (c : cls) (i j : nat) : tactic cls :=
if i > j then try_factor' gt c j i else try_factor' gt c i j

meta_definition try_infer_factor (c : active_cls) (i j : nat) : resolution_prover unit := do
f ← resolution_prover_of_tactic (try_factor gt c↣c i j),
ss ← resolution_prover_of_tactic $ does_subsume f c↣c,
add_inferred f,
if ss then remove_redundant c↣id else return ()

meta_definition factor_inf : inference :=
take given, do gt ← get_term_order, sequence' $ do
  i ← active_cls.selected given,
  j ← list.range (cls.num_lits given↣c),
  return $ try_infer_factor gt given i j <|> return ()
