import clause prover_state
open tactic monad

private meta def try_subsume_core : list cls.lit → list cls.lit → tactic unit
| [] _ := skip
| small large := first $ do
  i ← small↣zip_with_index, j ← large↣zip_with_index,
  return $ do
    unify_lit i.1 j.1,
    try_subsume_core (small↣remove i.2) (large↣remove j.2)

-- FIXME: this is incorrect if a quantifier is unused
meta def try_subsume (small large : cls) : tactic unit := do
small_open ← cls.open_metan small (cls.num_quants small),
large_open ← cls.open_constn large (cls.num_quants large),
guard $ small↣num_lits ≤ large↣num_lits,
try_subsume_core small_open↣1↣get_lits large_open↣1↣get_lits

meta def does_subsume (small large : cls) : tactic bool :=
(try_subsume small large >> return tt) <|> return ff

meta def any_tt {m : Type → Type} [monad m] (active : rb_map name active_cls) (pred : active_cls → m bool) : m bool :=
active↣fold (return ff) $ λk a cont, do
  v ← pred a, if v then return tt else cont

meta def any_tt_list {A} (pred : A → tactic bool) : list A → tactic bool
| [] := return ff
| (x::xs) := do v ← pred x, if v then return tt else any_tt_list xs

meta def forward_subsumption : inference := take given, do
active ← get_active,
any_tt active (λa,
  if a↣id = given↣id then return ff else do
  ss ← resolution_prover_of_tactic $ does_subsume a↣c given↣c,
  if ss then do
    remove_redundant given↣id [a],
    return tt
  else
    return ff),
return ()

meta def forward_subsumption_pre : resolution_prover unit := preprocessing_rule $ λnew, do
active ← get_active, resolution_prover_of_tactic $ filterM (λn,
  do ss ← any_tt active (λa, does_subsume a↣c n), return (bnot ss)) new

meta def subsumption_interreduction : list cls → tactic (list cls)
| (c::cs) := do
  c_subsumed_by_cs ← any_tt_list (λd, does_subsume d c) cs,
  if c_subsumed_by_cs then
    subsumption_interreduction cs
  else do
    cs_not_subsumed_by_c ← filterM (λd, liftM bnot (does_subsume c d)) cs,
    cs' ← subsumption_interreduction cs_not_subsumed_by_c,
    return (c::cs')
| [] := return []

meta def subsumption_interreduction_pre : resolution_prover unit :=
preprocessing_rule $ λnew,
let new' := list.sort_on cls.num_lits new in
resolution_prover_of_tactic $ subsumption_interreduction new'

meta def keys_where_tt (active : rb_map name active_cls) (pred : active_cls → tactic bool) : tactic (list name) :=
@rb_map.fold _ _ (tactic (list name)) active (return []) $ λk a cont, do
  v ← pred a, rest ← cont, return $ if v then k::rest else rest

meta def backward_subsumption : inference := λgiven, do
active ← get_active,
ss ← resolution_prover_of_tactic $
  keys_where_tt active (λa, does_subsume given↣c a↣c),
sequence' $ do id ← ss, guard (id ≠ given↣id), [remove_redundant id [given]]
