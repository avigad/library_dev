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
guard $ small↣num_lits ≤ large↣num_lits,
try_subsume_core (cls.get_lits small_open.1) (cls.get_lits large_open.1)

meta_definition does_subsume (small large : cls) : tactic bool :=
(try_subsume small large >> return tt) <|> return ff

meta_definition any_tt (active : rb_map name active_cls) (pred : active_cls → tactic bool) : tactic bool :=
rb_map.fold active (return ff) $ λk a cont, do
  v ← pred a, if v then return tt else cont

meta_definition any_tt_list {A} (pred : A → tactic bool) : list A → tactic bool
| [] := return ff
| (x::xs) := do v ← pred x, if v then return tt else any_tt_list xs

meta_definition forward_subsumption : inference := redundancy_inference $ λgiven, do
active ← get_active,
resolution_prover_of_tactic $ any_tt active (λa, do
  ss ← does_subsume (active_cls.c a) (active_cls.c given),
  return (decidable.to_bool (ss ∧ active_cls.id given ≠ active_cls.id a)))

meta_definition forward_subsumption_pre : resolution_prover unit := preprocessing_rule $ λnew, do
active ← get_active, resolution_prover_of_tactic $ filterM (λn,
  do ss ← any_tt active (λa, does_subsume (active_cls.c a) n), return (bool.bnot ss)) new

meta_definition subsumption_interreduction : list cls → tactic (list cls)
| (c::cs) := do
  c_subsumed_by_cs ← any_tt_list (λd, does_subsume d c) cs,
  if c_subsumed_by_cs then
    subsumption_interreduction cs
  else do
    cs_not_subsumed_by_c ← filterM (λd, liftM bool.bnot (does_subsume c d)) cs,
    cs' ← subsumption_interreduction cs_not_subsumed_by_c,
    return (c::cs')
| [] := return []

meta_definition subsumption_interreduction_pre : resolution_prover unit :=
preprocessing_rule $ λnew, resolution_prover_of_tactic (subsumption_interreduction new)

meta_definition keys_where_tt (active : rb_map name active_cls) (pred : active_cls → tactic bool) : tactic (list name) :=
@rb_map.fold _ _ (tactic (list name)) active (return []) $ λk a cont, do
  v ← pred a, rest ← cont, return $ if v then k::rest else rest

meta_definition backward_subsumption : inference := λgiven, do
active ← get_active,
ss ← resolution_prover_of_tactic $
  keys_where_tt active (λa, does_subsume (active_cls.c given) (active_cls.c a)),
sequence' $ do id ← ss, guard (id ≠ active_cls.id given), [remove_redundant id]
