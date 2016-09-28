import clause prover_state subsumption
open tactic expr monad

variable gt : expr → expr → bool

meta def inst_lit (c : cls) (i : nat) (e : expr) : tactic cls := do
opened ← cls.open_constn c i,
return $ cls.close_constn (cls.inst opened.1 e) opened.2

private meta def try_factor' (c : cls) (i j : nat) : tactic cls := do
qf ← cls.open_metan c c↣num_quants,
unify_lit (qf↣1↣get_lit i) (qf↣1↣get_lit j),
qfi ← cls.inst_mvars qf.1,
guard $ cls.is_maximal gt qfi i,
at_j ← cls.open_constn qf.1 j,
hyp_i ← option.to_monad (list.nth at_j.2 i),
cs ← sort_and_constify_metas qf.2,
qf' ← cls.inst_mvars $
  if cls.has_fin c ∧ j+1 = cls.num_lits c then
    cls.close_constn (cls.of_proof_and_type (app hyp_i at_j.1↣prf) (const ``false [])) at_j.2
  else
    cls.close_constn (cls.inst at_j.1 hyp_i) at_j.2,
return $ cls.close_constn qf' cs

meta def try_factor (c : cls) (i j : nat) : tactic cls :=
if i > j then try_factor' gt c j i else try_factor' gt c i j

meta def try_infer_factor (c : active_cls) (i j : nat) : resolution_prover unit := do
f ← resolution_prover_of_tactic (try_factor gt c↣c i j),
ss ← resolution_prover_of_tactic $ does_subsume f c↣c,
add_inferred f [c],
if ss then remove_redundant c↣id [] else return ()

meta def factor_inf : inference :=
take given, do gt ← get_term_order, sequence' $ do
  i ← active_cls.selected given,
  j ← list.range given↣c↣num_lits,
  return $ try_infer_factor gt given i j <|> return ()

meta def factor_dup_lits' : cls → tactic cls | c :=
match (do i ← c↣get_lits↣zip_with_index,
          j ← c↣get_lits↣zip_with_index,
          guard $ i↣2 < j↣2,
          guard $ i↣1 = j↣1,
          [(i↣2,j↣2)]) with
| ((i,j)::_) := try_factor (λx y, ff) c i j >>= factor_dup_lits'
| [] := return c
end

meta def factor_dup_lits (c : cls) : tactic cls := do
qf ← c↣open_constn c↣num_quants,
qf' ← factor_dup_lits' qf↣1,
return $ qf'↣close_constn qf↣2

meta def factor_dup_lits_pre := preprocessing_rule $ take new, do
resolution_prover_of_tactic $ mapM factor_dup_lits new
