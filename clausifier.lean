import clause
import prover_state
open expr list tactic monad decidable

lemma clause_of_formula {p} : p → ¬¬p := λx y, y x

meta_definition head_lit_rule := cls.lit → cls → tactic (option (list cls))

lemma false_r {c} : (¬false → c) → c := λnfc, nfc (λx, x)
meta_definition inf_false_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
if cls.lit.is_pos l = tt ∧ is_false (cls.lit.formula l) = tt then do
  prf' ← mk_mapp ``false_r [none, some (cls.prf c)],
  return $ some [cls.mk 0 (cls.num_lits c - 1) prf' (binding_body (cls.type c))]
else
  return none

lemma true_l {c} : (true → c) → c := λtc, tc true.intro
meta_definition is_true_const (e : expr) : bool := to_bool (is_constant_of e ``true = tt)
meta_definition inf_true_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
if cls.lit.is_neg l = tt ∧ is_true_const (cls.lit.formula l) = tt then do
  prf' ← mk_mapp ``true_l [none, some (cls.prf c)],
  return $ some [cls.mk 0 (cls.num_lits c - 1) prf' (binding_body (cls.type c))]
else
  return none

lemma not_r {a c} : (¬¬a → c) → (a → c) := λnnac a, nnac (clause_of_formula a)
meta_definition inf_not_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match (cls.lit.is_pos l, is_not (cls.lit.formula l)) with
| (tt, some a) := do
  prf' ← mk_mapp ``not_r [none, none, some (cls.prf c)],
  return $ some [cls.mk 0 (cls.num_lits c) prf' (imp a (binding_body (cls.type c)))]
| _ := return none
end

lemma and_l {a b c} : ((a ∧ b) → c) → (a → b → c) := λabc a b, abc (and.intro a b)
meta_definition inf_and_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.neg (app (app (const and_name _) a) b) :=
  if and_name = ``and then do
    prf' ← mk_mapp ``and_l [none, none, none, some (cls.prf c)],
    return $ some [cls.mk 0 (cls.num_lits c + 1) prf' (imp a (imp b (binding_body (cls.type c))))]
  else return none
| _ := return none
end

lemma and_r1 {a b c} : (¬(a ∧ b) → c) → (¬a → c) := λnabc na, nabc (λab, na (and.left ab))
lemma and_r2 {a b c} : (¬(a ∧ b) → c) → (¬b → c) := λnabc na, nabc (λab, na (and.right ab))
meta_definition inf_and_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.neg (app (app (const and_name _) a) b) :=
  if and_name = ``and then do
    prf₁ ← mk_mapp ``and_r1 [none, none, none, some (cls.prf c)],
    prf₂ ← mk_mapp ``and_r2 [none, none, none, some (cls.prf c)],
    na ← mk_mapp ``not [some a],
    nb ← mk_mapp ``not [some b],
    return $ some [
      cls.mk 0 (cls.num_lits c) prf₁ (imp na (binding_body (cls.type c))),
      cls.mk 0 (cls.num_lits c) prf₂ (imp nb (binding_body (cls.type c)))
    ]
  else return none
| _ := return none
end

lemma or_r {a b c} : (¬(a ∨ b) → c) → (¬a → ¬b → c) := λnabc na nb, nabc (λab, or.elim ab na nb)
meta_definition inf_or_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.pos (app (app (const or_name _) a) b) :=
  if or_name = ``or then do
    na ← mk_mapp ``not [some a],
    nb ← mk_mapp ``not [some b],
    prf' ← mk_mapp ``or_r [none, none, none, some (cls.prf c)],
    return $ some [cls.mk 0 (cls.num_lits c + 1) prf' (imp na (imp nb (binding_body (cls.type c))))]
  else return none
| _ := return none
end

lemma or_l1 {a b c} : ((a ∨ b) → c) → (a → c) := λabc a, abc (or.inl a)
lemma or_l2 {a b c} : ((a ∨ b) → c) → (b → c) := λabc b, abc (or.inr b)
meta_definition inf_or_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.neg (app (app (const or_name _) a) b) :=
  if or_name = ``or then do
    prf₁ ← mk_mapp ``or_l1 [none, none, none, some (cls.prf c)],
    prf₂ ← mk_mapp ``or_l2 [none, none, none, some (cls.prf c)],
    return $ some [
      cls.mk 0 (cls.num_lits c) prf₁ (imp a (binding_body (cls.type c))),
      cls.mk 0 (cls.num_lits c) prf₂ (imp b (binding_body (cls.type c)))
    ]
  else return none
| _ := return none
end

lemma imp_r {a b c} : (¬(a → b) → c) → (a → ¬b → c) := λnabc a nb, nabc (λab, absurd (ab a) nb)
meta_definition inf_imp_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.pos (pi _ _ a b) :=
  if has_var b = ff then do
    nb ← mk_mapp ``not [some b],
    prf' ← mk_mapp ``imp_r [none, none, none, some (cls.prf c)],
    return $ some [cls.mk 0 (cls.num_lits c + 1) prf' (imp a (imp nb (binding_body (cls.type c))))]
  else return none
| _ := return none
end

lemma imp_l1 {a b c} : ((a → b) → c) → (¬a → c) := λabc na, abc (λa, absurd a na)
lemma imp_l2 {a b c} : ((a → b) → c) → (b → c) := λabc b, abc (λa, b)
meta_definition inf_imp_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.neg (pi _ _ a b) :=
  if has_var b = ff then do
    prf₁ ← mk_mapp ``imp_l1 [none, none, none, some (cls.prf c)],
    prf₂ ← mk_mapp ``imp_l2 [none, none, none, some (cls.prf c)],
    na ← mk_mapp ``not [some a],
    return $ some [
      cls.mk 0 (cls.num_lits c) prf₁ (imp na (binding_body (cls.type c))),
      cls.mk 0 (cls.num_lits c) prf₂ (imp b (binding_body (cls.type c)))
    ]
  else return none
| _ := return none
end

meta_definition first_some {a} : list (tactic (option a)) → tactic (option a)
| [] := return none
| (x::xs) := do xres ← x, match xres with some y := return (some y) | none := first_some xs end

meta_definition clausification_rules : list head_lit_rule :=
[ inf_false_r, inf_true_l, inf_not_r,
  inf_and_l, inf_and_r,
  inf_or_l, inf_or_r,
  inf_imp_l, inf_imp_r ]

meta_definition clausify_at (c : cls) (i : nat) : tactic (option (list cls)) :=
do opened ← cls.open_constn c (cls.num_quants c + i),
lit ← return $ cls.get_lit opened.1 0,
maybe_clausified ← first_some (map (λr, r lit opened.1) clausification_rules),
match maybe_clausified with
| none := return none
| some clsfd := return (some (map (λc', cls.close_constn c' opened.2) clsfd))
end

meta_definition clausification_inference_core (c : cls) : tactic (option (list cls)) :=
first_some (map (clausify_at c) (range (cls.num_lits c)))

meta_definition clausification_inference : inference := λgiven, do
one_step_clausified ← resolution_prover_of_tactic $ clausification_inference_core (active_cls.c given),
match one_step_clausified with
| some simpld := do forM' simpld add_inferred, remove_redundant (active_cls.id given)
| none := return ()
end
