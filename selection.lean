import prover_state

meta def non_assertion_lits (pc : passive_cls) : list ℕ :=
do i ← list.range pc↣c↣num_lits, guard $ i ∉ pc↣assertions, [i]

meta def dumb_selection : selection_strategy :=
λpc, return $ match do i ← non_assertion_lits pc, guard $ (pc↣c↣get_lit i)↣is_neg, [i] with
| [] := non_assertion_lits pc
| neg_lit::_ := [neg_lit]
end

meta def selection21 : selection_strategy := take pc, do
gt ← get_term_order,
maximal_lits ← return $ list.filter_maximal (λi j,
  gt (cls.lit.formula $ cls.get_lit pc↣c i) (cls.lit.formula $ cls.get_lit pc↣c j)) (non_assertion_lits pc),
if list.length maximal_lits = 1 then return maximal_lits else do
neg_lits ← return $ list.filter (λi, cls.lit.is_neg (cls.get_lit pc↣c i)) (non_assertion_lits pc),
maximal_neg_lits ← return $ list.filter_maximal (λi j,
  gt (cls.lit.formula $ cls.get_lit pc↣c i) (cls.lit.formula $ cls.get_lit pc↣c j)) neg_lits,
if ¬list.empty maximal_neg_lits then
  return (list.taken 1 maximal_neg_lits)
else
  return maximal_lits
meta def selection22 : selection_strategy := take pc, do
gt ← get_term_order,
maximal_lits ← return $ list.filter_maximal (λi j,
  gt (cls.lit.formula $ cls.get_lit pc↣c i) (cls.lit.formula $ cls.get_lit pc↣c j)) (non_assertion_lits pc),
maximal_lits_neg ← return $ list.filter (λi, cls.lit.is_neg (cls.get_lit pc↣c i)) maximal_lits,
if ¬list.empty maximal_lits_neg then
  return (list.taken 1 maximal_lits_neg)
else
  return maximal_lits

meta def clause_weight (c : cls) : nat :=
40 * cls.num_lits c + expr_size (cls.type c)

meta def find_minimal_by (passive : rb_map name passive_cls) (f : name → cls → ℕ) : name :=
match @rb_map.fold _ _ (option (name × ℕ)) passive none
      (λk c acc, let w := f k c↣c in
                 match acc with
                 | none := some (k, w)
                 | (some (n,s)) :=
                         if w < s then
                            some (k, w)
                         else
                            acc
                         end)
with
| none := name.anonymous
| some (n,_) := n
end

meta def age_of_clause_id : name → ℕ
| (name.mk_numeral i _) := unsigned.to_nat i
| _ := 0

meta def find_minimal_weight (passive : rb_map name passive_cls) : name :=
find_minimal_by passive (λn c, 100 * clause_weight c + age_of_clause_id n)

meta def find_minimal_age (passive : rb_map name passive_cls) : name :=
find_minimal_by passive (λn c, age_of_clause_id n)

meta def weight_clause_selection : clause_selection_strategy :=
take iter, do state ← stateT.read, return $ find_minimal_weight state↣passive

meta def oldest_clause_selection : clause_selection_strategy :=
take iter, do state ← stateT.read, return $ find_minimal_age state↣passive

meta def age_weight_clause_selection (thr mod : ℕ) : clause_selection_strategy :=
take iter, if iter % mod < thr then
              weight_clause_selection iter
           else
              oldest_clause_selection iter
