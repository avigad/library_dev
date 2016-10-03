import .clause .prover_state .subsumption
open tactic expr monad

namespace super

variable gt : expr → expr → bool

meta def inst_lit (c : clause) (i : nat) (e : expr) : tactic clause := do
opened ← clause.open_constn c i,
return $ clause.close_constn (clause.inst opened.1 e) opened.2

private meta def try_factor' (c : clause) (i j : nat) : tactic clause := do
qf ← clause.open_metan c c↣num_quants,
unify_lit (qf↣1↣get_lit i) (qf↣1↣get_lit j),
qfi ← clause.inst_mvars qf.1,
guard $ clause.is_maximal gt qfi i,
at_j ← clause.open_constn qf.1 j,
hyp_i ← option.to_monad (list.nth at_j.2 i),
clause.meta_closure qf↣2 $ (at_j↣1↣inst hyp_i)↣close_constn at_j↣2

meta def try_factor (c : clause) (i j : nat) : tactic clause :=
if i > j then try_factor' gt c j i else try_factor' gt c i j

meta def try_infer_factor (c : active_cls) (i j : nat) : resolution_prover unit := do
f ← ↑(try_factor gt c↣c i j),
ss : bool ← ↑(does_subsume f c↣c),
add_inferred f [c],
if ss then remove_redundant c↣id [] else return ()

meta def factor_inf : inference :=
take given, do gt ← get_term_order, sequence' $ do
  i ← active_cls.selected given,
  j ← list.range given↣c↣num_lits,
  return $ try_infer_factor gt given i j <|> return ()

meta def factor_dup_lits' : clause → tactic clause | c :=
match (do i ← c↣get_lits↣zip_with_index,
          j ← c↣get_lits↣zip_with_index,
          guard $ i↣2 < j↣2,
          guard $ i↣1 = j↣1,
          [(i↣2,j↣2)]) with
| ((i,j)::_) := try_factor (λx y, ff) c i j >>= factor_dup_lits'
| [] := return c
end

meta def factor_dup_lits (c : clause) : tactic clause := do
qf ← c↣open_constn c↣num_quants,
qf' ← factor_dup_lits' qf↣1,
return $ qf'↣close_constn qf↣2

meta def factor_dup_lits_pre := preprocessing_rule $ take new, do
↑(mapM factor_dup_lits new)

end super
