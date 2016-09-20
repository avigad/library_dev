import clause prover_state
open tactic monad

private meta_definition try_subsume_core : list cls.lit → list cls.lit → tactic unit
| [] _ := skip
| small large := first $ do
  i ← list.zip_with_index small,
  j ← list.zip_with_index large,
  return $ do
    unify_lit i.1 j.1,
    try_subsume_core (list.remove small i.2) (list.remove large j.2)

-- FIXME: this is incorrect if a quantifier is unused
meta_definition try_subsume (small large : cls) : tactic unit := do
small_open ← cls.open_metan small (cls.num_quants small),
large_open ← cls.open_constn large (cls.num_quants large),
try_subsume_core (cls.get_lits small_open.1) (cls.get_lits large_open.1)

meta_definition does_subsume (small large : cls) : tactic bool :=
(try_subsume small large >> return tt) <|> return ff

meta_definition any_tt (active : rb_map name active_cls) (pred : active_cls → tactic bool) : tactic bool :=
rb_map.fold active (return ff) $ λk a cont, do
  v ← pred a, if v = tt then return tt else cont

meta_definition forward_subsumption : inference := redundancy_inference $ λgiven, do
active ← get_active,
resolution_prover_of_tactic $ any_tt active (λa, do
  ss ← does_subsume (active_cls.c a) (active_cls.c given),
  return (decidable.to_bool (ss = tt ∧ active_cls.id given ≠ active_cls.id a)))

meta_definition forward_subsumption_pre : resolution_prover unit := preprocessing_rule $ λnew, do
active ← get_active, resolution_prover_of_tactic $ filterM (λn,
  do ss ← any_tt active (λa, does_subsume (active_cls.c a) n), return (bool.bnot ss)) new

meta_definition subsumption_interreduction : list cls → tactic (list cls)
| (c::cs) := do
  which_cs_subsume_c ← @mapM tactic _ _ _ (λd, does_subsume d c) cs,
  if list.bor which_cs_subsume_c = tt then
    subsumption_interreduction cs
  else do
    cs_not_subsumed_by_c ← filterM (λd, do ss ← does_subsume c d, return (bool.bnot ss)) cs,
    cs' ← subsumption_interreduction cs_not_subsumed_by_c,
    return (c::cs')
| [] := return []

meta_definition subsumption_interreduction_pre : resolution_prover unit :=
preprocessing_rule $ λnew, resolution_prover_of_tactic (subsumption_interreduction new)

meta_definition keys_where_tt (active : rb_map name active_cls) (pred : active_cls → tactic bool) : tactic (list name) :=
@rb_map.fold _ _ (tactic (list name)) active (return []) $ λk a cont, do
  v ← pred a, rest ← cont, return $ if v = tt then k::rest else rest

meta_definition backward_subsumption : inference := λgiven, do
active ← get_active,
ss ← resolution_prover_of_tactic $
  keys_where_tt active (λa, does_subsume (active_cls.c given) (active_cls.c a)),
@forM' resolution_prover _ _ _ (list.filter (λid, id ≠ active_cls.id given) ss) remove_redundant
