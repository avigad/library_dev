import clause
import prover_state
open expr list tactic monad decidable

lemma clause_of_formula {p} : p → ¬¬p := λx y, y x

meta_definition head_lit_rule := cls.lit → cls → tactic (option (list cls))

meta_definition inf_false_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
if cls.lit.is_neg l = tt ∧ is_false (cls.lit.formula l) = tt then
  return (some [])
else
  return none

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

meta_definition inf_true_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
if cls.lit.is_pos l = tt ∧ is_true_const (cls.lit.formula l) = tt then
  return (some [])
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
| cls.lit.pos (app (app (const and_name _) a) b) :=
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

lemma all_r {a b c} : (¬(∀x:a, b x) → c) → (∀x:a, ¬b x → c) := λnabc a nb, nabc (λab, absurd (ab a) nb)
meta_definition inf_all_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.pos (pi n bi a b) := do
    nb ← mk_mapp ``not [some b],
    prf' ← mk_mapp ``all_r [none, none, none, some (cls.prf c)],
    return $ some [cls.mk 1 (cls.num_lits c) prf' (pi n bi a (imp nb (binding_body (cls.type c))))]
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

lemma ex_l {a b c} : ((∃x:a, b x) → c) → (∀x:a, b x → c) := λeabc a b, eabc (exists.intro a b)
meta_definition inf_ex_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.neg (app (app (const ex_name _) d) p) :=
  if ex_name = ``Exists then do
    prf' ← mk_mapp ``ex_l [none, none, none, some (cls.prf c)],
    n ← mk_fresh_name, -- FIXME: (binding_name p) produces ugly [anonymous] output
    return $ some [cls.mk 1 (cls.num_lits c) prf'
      (pi n binder_info.default d
        (imp (app p (mk_var 0)) (binding_body (cls.type c))))]
  else return none
| _ := return none
end

lemma demorgan {a b} : (¬∃x:a, ¬b x) → ∀x, b x :=
take nenb x, classical.by_contradiction (take nbx, nenb (exists.intro x nbx))
lemma all_l {a b c} : ((∀x:a, b x) → c) → ((¬∃x:a, ¬b x) → c) :=
λabc nanb, abc (demorgan nanb)
meta_definition inf_all_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.neg (pi n bi a b) := do
    nb ← mk_mapp ``not [some b],
    enb ← mk_mapp ``Exists [none, some $ lam n binder_info.default a nb],
    nenb ← mk_mapp ``not [some enb],
    prf' ← mk_mapp ``all_l [none, none, none, some (cls.prf c)],
    return $ some [cls.mk 0 (cls.num_lits c) prf' (imp nenb (binding_body (cls.type c)))]
| _ := return none
end

lemma helper_r {a b c} : (a → b) → (¬a → c) → (¬b → c) := λab nac nb, nac (λa, nb (ab a))
meta_definition inf_ex_r (ctx : list expr) (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.pos (app (app (const ex_name _) d) p) :=
  if ex_name = ``Exists then do
    sk_sym_name ← mk_fresh_name, -- FIXME: (binding_name p) produces ugly [anonymous] output
    inh_name ← mk_fresh_name,
    inh_lc ← return $ local_const inh_name inh_name binder_info.implicit d,
    sk_sym ← return $ local_const sk_sym_name sk_sym_name binder_info.default (pis (ctx ++ [inh_lc]) d),
    sk_p ← return $ app p (app_of_list sk_sym (ctx ++ [inh_lc])),
    sk_ax ← mk_mapp ``Exists [some (local_type sk_sym),
      some (lambdas [sk_sym] (pis (ctx ++ [inh_lc]) (imp (cls.lit.formula l) sk_p)))],
    sk_ax_name ← mk_fresh_name, assert sk_ax_name sk_ax,
    nonempt_of_inh ← mk_mapp ``nonempty.intro [some d, some inh_lc],
    eps ← mk_mapp ``classical.epsilon [some d, some nonempt_of_inh, some p],
    existsi (lambdas (ctx ++ [inh_lc]) eps),
    eps_spec ← mk_mapp ``classical.epsilon_spec [some d, some p],
    exact (lambdas (ctx ++ [inh_lc]) eps_spec),
    sk_ax_local ← get_local sk_ax_name, cases_using sk_ax_local [sk_sym_name, sk_ax_name],
    sk_ax' ← get_local sk_ax_name, sk_sym' ← get_local sk_sym_name,
    sk_p' ← whnf $ app p (app_of_list sk_sym (ctx ++ [inh_lc])),
    not_sk_p' ← mk_mapp ``not [some sk_p'],
    prf' ← mk_mapp ``helper_r [none, none, none, some (app_of_list sk_ax' (ctx ++ [inh_lc])), some (cls.prf c)],
    return $ some [cls.mk 1 (cls.num_lits c)
      (lambdas [inh_lc] prf')
      (pis [inh_lc] (imp not_sk_p' (binding_body (cls.type c))))]
else return none
| _ := return none
end

meta_definition first_some {a} : list (tactic (option a)) → tactic (option a)
| [] := return none
| (x::xs) := do xres ← x, match xres with some y := return (some y) | none := first_some xs end

meta_definition clausification_rules (ctx : list expr) : list head_lit_rule :=
[ inf_false_l, inf_false_r, inf_true_l, inf_true_r,
  inf_not_r,
  inf_and_l, inf_and_r,
  inf_or_l, inf_or_r,
  inf_imp_l, inf_all_r,
  inf_ex_l,
  inf_all_l, inf_ex_r ctx ]

meta_definition clausify_at (c : cls) (i : nat) : tactic (option (list cls)) := do
opened ← cls.open_constn c (cls.num_quants c + i),
lit ← return $ cls.get_lit opened.1 0,
maybe_clausified ← first_some (map (λr, r lit opened.1)
  (clausification_rules (list.taken (cls.num_quants c) opened.2))),
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
