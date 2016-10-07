import .clause .prover_state
open tactic monad

namespace super

private meta def try_subsume_core : list clause.literal → list clause.literal → tactic unit
| [] _ := skip
| small large := first $ do
  i ← small↣zip_with_index, j ← large↣zip_with_index,
  return $ do
    unify_lit i.1 j.1,
    try_subsume_core (small↣remove i.2) (large↣remove j.2)

-- FIXME: this is incorrect if a quantifier is unused
meta def try_subsume (small large : clause) : tactic unit := do
small_open ← clause.open_metan small (clause.num_quants small),
large_open ← clause.open_constn large (clause.num_quants large),
guard $ small↣num_lits ≤ large↣num_lits,
try_subsume_core small_open↣1↣get_lits large_open↣1↣get_lits

meta def does_subsume (small large : clause) : tactic bool :=
(try_subsume small large >> return tt) <|> return ff

meta def does_subsume_with_assertions (small large : clause) : prover bool := do
small_ass ← collect_ass_hyps small,
large_ass ← collect_ass_hyps large,
if small_ass↣subset_of large_ass then do
  ♯ does_subsume small large
else
  return ff

meta def any_tt {m : Type → Type} [monad m] (active : rb_map name active_cls) (pred : active_cls → m bool) : m bool :=
active↣fold (return ff) $ λk a cont, do
  v ← pred a, if v then return tt else cont

meta def any_tt_list {m : Type → Type} [monad m] {A} (pred : A → m bool) : list A → m bool
| [] := return ff
| (x::xs) := do v ← pred x, if v then return tt else any_tt_list xs

meta def forward_subsumption : inference := take given, do
active ← get_active,
any_tt active (λa,
  if a↣id = given↣id then return ff else do
  ss ← ♯ does_subsume a↣c given↣c,
  if ss then do
    remove_redundant given↣id [a],
    return tt
  else
    return ff),
return ()

meta def forward_subsumption_pre : prover unit := preprocessing_rule $ λnew, do
active ← get_active, filterM (λn, do
  n_ass ← collect_ass_hyps n,
  do ss ← any_tt active (λa,
        if a↣assertions↣subset_of n_ass then do
          ♯ does_subsume a↣c n
        else
          return ff),
     return (bnot ss)) new

meta def subsumption_interreduction : list clause → prover (list clause)
| (c::cs) := do
  c_subsumed_by_cs ← any_tt_list (λd, does_subsume_with_assertions d c) cs,
  if c_subsumed_by_cs then
    subsumption_interreduction cs
  else do
    cs_not_subsumed_by_c ← filterM (λd, liftM bnot (does_subsume_with_assertions c d)) cs,
    cs' ← subsumption_interreduction cs_not_subsumed_by_c,
    return (c::cs')
| [] := return []

meta def subsumption_interreduction_pre : prover unit :=
preprocessing_rule $ λnew,
let new' := list.sort_on clause.num_lits new in
subsumption_interreduction new'

meta def keys_where_tt {m} [monad m] (active : rb_map name active_cls) (pred : active_cls → m bool) : m (list name) :=
@rb_map.fold _ _ (m (list name)) active (return []) $ λk a cont, do
  v ← pred a, rest ← cont, return $ if v then k::rest else rest

meta def backward_subsumption : inference := λgiven, do
active ← get_active,
ss ← ♯ keys_where_tt active (λa, does_subsume given↣c a↣c),
sequence' $ do id ← ss, guard (id ≠ given↣id), [remove_redundant id [given]]

end super
