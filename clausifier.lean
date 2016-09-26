import clause
import prover_state
open expr list tactic monad decidable

meta def head_lit_rule := cls.lit → cls → tactic (option (list cls))

meta def inf_whnf (l : cls.lit) (c : cls) : tactic (option (list cls)) := do
normalized ← whnf l↣formula,
if normalized = l↣formula then return none else
match l with
| cls.lit.final _ := return $ some [{ c with type := normalized }]
| cls.lit.left _ := return $ some [{ c with type := imp normalized c↣type↣binding_body }]
| cls.lit.right _ := return $ some [{ c with type := imp normalized↣not_ c↣type↣binding_body }]
end

meta def inf_false_f (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.final (const false_name _) :=
  if false_name = ``false then
    return (some [{ c with has_fin := ff, num_lits := 0 }])
  else
    return none
| _ := return none
end

meta def inf_true_f (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.final (const true_name _) :=
  if true_name = ``true then
    return (some [])
  else
    return none
| _ := return none
end

meta def inf_not_f (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.final (app (const not_name _) a) :=
  if not_name = ``not then do
    return $ some [{ c with has_fin := ff, type := imp a (const ``false []) }]
  else
    return none
| _ := return none
end

meta def inf_imp_f (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.final (pi _ _ _ _) :=
    return $ some [{ c with num_lits := 2 }]
| _ := return none
end

set_option eqn_compiler.max_steps 500

meta def inf_ex_f (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.final (app (app (const exists_name _) d) p) :=
  if exists_name = ``Exists then do
    c' ← cls.fin_to_pos c,
    return $ some [c']
  else
    return none
| _ := return none
end

lemma or_f {a b} : a ∨ b → (¬a → b) := or.resolve_left
meta def inf_or_f (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.final (app (app (const or_name _) a) b) :=
  if or_name = ``or then do
    prf' ← mk_mapp ``or_f [none, none, some c↣prf],
    return $ some [{ c with num_lits := 2, prf := prf', type := imp (app (const ``not []) a) b }]
  else return none
| _ := return none
end

meta def inf_false_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.left (const false_name _) :=
  if false_name = ``false then
     return (some [])
   else
     return none
| _ :=  return none
end

lemma false_r {c} : (¬false → c) → c := λnfc, nfc (λx, x)
meta def inf_false_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.right (const false_name _) :=
if false_name = ``false then do
  prf' ← mk_mapp ``false_r [none, some c↣prf],
  return $ some [{ c with num_lits := c↣num_lits - 1, prf := prf', type := binding_body c↣type }]
else
  return none
| _ := return none
end

lemma true_l {c} : (true → c) → c := λtc, tc true.intro
meta def inf_true_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.left (const true_name _) :=
if true_name = ``true then do
  prf' ← mk_mapp ``true_l [none, some c↣prf],
  return $ some [{ c with num_lits := c↣num_lits - 1, prf := prf', type := binding_body c↣type }]
else
  return none
| _ := return none
end

meta def inf_true_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.right (const true_name _) :=
if true_name = ``true then do
  return (some [])
else
  return none
| _ := return none
end

lemma not_r {a c} : (¬¬a → c) → (a → c) := λnnac a, nnac (λx, x a)
meta def inf_not_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match (l, is_not (cls.lit.formula l)) with
| (cls.lit.right _, some a) := do
  prf' ← mk_mapp ``not_r [none, none, some c↣prf],
  return $ some [{ c with prf := prf', type := imp a (binding_body c↣type) }]
| _ := return none
end

lemma and_l {a b c} : ((a ∧ b) → c) → (a → b → c) := λabc a b, abc (and.intro a b)
meta def inf_and_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.left (app (app (const and_name _) a) b) :=
  if and_name = ``and then do
    prf' ← mk_mapp ``and_l [none, none, none, some c↣prf],
    return $ some [{ c with num_lits := c↣num_lits + 1, prf := prf', type := imp a (imp b (binding_body c↣type)) }]
  else return none
| _ := return none
end

lemma and_r1 {a b c} : (¬(a ∧ b) → c) → (¬a → c) := λnabc na, nabc (λab, na (and.left ab))
lemma and_r2 {a b c} : (¬(a ∧ b) → c) → (¬b → c) := λnabc na, nabc (λab, na (and.right ab))
meta def inf_and_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.right (app (app (const and_name _) a) b) :=
  if and_name = ``and then do
    prf₁ ← mk_mapp ``and_r1 [none, none, none, some c↣prf],
    prf₂ ← mk_mapp ``and_r2 [none, none, none, some c↣prf],
    na ← mk_mapp ``not [some a],
    nb ← mk_mapp ``not [some b],
    return $ some [
      { c with prf := prf₁, type := imp na (binding_body c↣type) },
      { c with prf := prf₂, type := imp nb (binding_body c↣type) }
    ]
  else return none
| _ := return none
end

lemma or_r {a b c} : (¬(a ∨ b) → c) → (¬a → ¬b → c) := λnabc na nb, nabc (λab, or.elim ab na nb)
meta def inf_or_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.right (app (app (const or_name _) a) b) :=
  if or_name = ``or then do
    na ← mk_mapp ``not [some a],
    nb ← mk_mapp ``not [some b],
    prf' ← mk_mapp ``or_r [none, none, none, some c↣prf],
    return $ some [{ c with num_lits := c↣num_lits + 1, prf := prf', type := imp na (imp nb (binding_body c↣type)) }]
  else return none
| _ := return none
end

lemma or_l1 {a b c} : ((a ∨ b) → c) → (a → c) := λabc a, abc (or.inl a)
lemma or_l2 {a b c} : ((a ∨ b) → c) → (b → c) := λabc b, abc (or.inr b)
meta def inf_or_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.left (app (app (const or_name _) a) b) :=
  if or_name = ``or then do
    prf₁ ← mk_mapp ``or_l1 [none, none, none, some c↣prf],
    prf₂ ← mk_mapp ``or_l2 [none, none, none, some c↣prf],
    return $ some [
      { c with prf := prf₁, type := imp a (binding_body c↣type) },
      { c with prf := prf₂, type := imp b (binding_body c↣type) }
    ]
  else return none
| _ := return none
end

lemma all_r {a} {b : a → Prop} {c} : (¬(∀x:a, b x) → c) → (∀x:a, ¬b x → c) := λnabc a nb, nabc (λab, absurd (ab a) nb)
meta def inf_all_r (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.right (pi n bi a b) := do
    nb ← mk_mapp ``not [some b],
    prf' ← mk_mapp ``all_r [none, none, none, some c↣prf],
    return $ some [{ c with num_quants := 1, prf := prf', type := pi n bi a (imp nb (binding_body c↣type)) }]
| _ := return none
end

lemma imp_l1 {a b c} : ((a → b) → c) → (¬a → c) := λabc na, abc (λa, absurd a na)
lemma imp_l2 {a b c} : ((a → b) → c) → (b → c) := λabc b, abc (λa, b)
meta def inf_imp_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.left (pi _ _ a b) :=
  if ¬has_var b then do
    prf₁ ← mk_mapp ``imp_l1 [none, none, none, some c↣prf],
    prf₂ ← mk_mapp ``imp_l2 [none, none, none, some c↣prf],
    na ← mk_mapp ``not [some a],
    return $ some [
      { c with prf := prf₁, type := imp na (binding_body c↣type) },
      { c with prf := prf₂, type := imp b (binding_body c↣type) }
    ]
  else return none
| _ := return none
end

lemma ex_l {a} {b : a → Prop} {c} : ((∃x:a, b x) → c) → (∀x:a, b x → c) := λeabc a b, eabc (exists.intro a b)
meta def inf_ex_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.left (app (app (const ex_name _) d) p) :=
  if ex_name = ``Exists then do
    prf' ← mk_mapp ``ex_l [none, none, none, some c↣prf],
    n ← mk_fresh_name, -- FIXME: (binding_name p) produces ugly [anonymous] output
    px ← whnf $ app p (mk_var 0),
    return $ some [{ c with num_quants := 1, prf := prf',
      type := pi n binder_info.default d (imp px (binding_body c↣type)) }]
  else return none
| _ := return none
end

lemma demorgan {a} {b : a → Prop} : (¬∃x:a, ¬b x) → ∀x, b x :=
take nenb x, classical.by_contradiction (take nbx, nenb (exists.intro x nbx))
lemma all_l {a} {b : a → Prop} {c} : ((∀x:a, b x) → c) → ((¬∃x:a, ¬b x) → c) :=
λabc nanb, abc (demorgan nanb)
meta def inf_all_l (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.left (pi n bi a b) := do
    nb ← mk_mapp ``not [some b],
    enb ← mk_mapp ``Exists [none, some $ lam n binder_info.default a nb],
    nenb ← mk_mapp ``not [some enb],
    prf' ← mk_mapp ``all_l [none, none, none, some c↣prf],
    return $ some [{ c with prf := prf', type := imp nenb (binding_body c↣type) }]
| _ := return none
end

lemma helper_r {a b c} : (a → b) → (¬a → c) → (¬b → c) := λab nac nb, nac (λa, nb (ab a))
meta def inf_ex_r (ctx : list expr) (l : cls.lit) (c : cls) : tactic (option (list cls)) :=
match l with
| cls.lit.right (app (app (const ex_name _) d) p) :=
  if ex_name = ``Exists then do
    sk_sym_name_pp ← get_unused_name `sk (some 1), sk_sym_name ← mk_fresh_name,
    inh_name ← mk_fresh_name,
    inh_lc ← return $ local_const inh_name inh_name binder_info.implicit d,
    sk_sym ← return $ local_const sk_sym_name sk_sym_name_pp binder_info.default (pis (ctx ++ [inh_lc]) d),
    sk_p ← whnf_core transparency.none $ app p (app_of_list sk_sym (ctx ++ [inh_lc])),
    sk_ax ← mk_mapp ``Exists [some (local_type sk_sym),
      some (lambdas [sk_sym] (pis (ctx ++ [inh_lc]) (imp (cls.lit.formula l) sk_p)))],
    sk_ax_name ← get_unused_name `sk_axiom (some 1), assert sk_ax_name sk_ax,
    nonempt_of_inh ← mk_mapp ``nonempty.intro [some d, some inh_lc],
    eps ← mk_mapp ``classical.epsilon [some d, some nonempt_of_inh, some p],
    existsi (lambdas (ctx ++ [inh_lc]) eps),
    eps_spec ← mk_mapp ``classical.epsilon_spec [some d, some p],
    exact (lambdas (ctx ++ [inh_lc]) eps_spec),
    sk_ax_local ← get_local sk_ax_name, cases_using sk_ax_local [sk_sym_name_pp, sk_ax_name],
    sk_ax' ← get_local sk_ax_name, sk_sym' ← get_local sk_sym_name_pp,
    sk_p' ← whnf_core transparency.none $ app p (app_of_list sk_sym' (ctx ++ [inh_lc])),
    not_sk_p' ← mk_mapp ``not [some sk_p'],
    prf' ← mk_mapp ``helper_r [none, none, none, some (app_of_list sk_ax' (ctx ++ [inh_lc])), some c↣prf],
    return $ some [{ c with num_quants := 1, prf := lambdas [inh_lc] prf',
      type := pis [inh_lc] (imp not_sk_p' (binding_body c↣type)) }]
else return none
| _ := return none
end

meta def first_some {a : Type} : list (tactic (option a)) → tactic (option a)
| [] := return none
| (x::xs) := do xres ← x, match xres with some y := return (some y) | none := first_some xs end

meta def clausification_rules (ctx : list expr) : list head_lit_rule :=
[ inf_false_f, inf_true_f, inf_not_f, inf_imp_f, inf_or_f, inf_ex_f,
  inf_false_l, inf_false_r, inf_true_l, inf_true_r,
  inf_not_r,
  inf_and_l, inf_and_r,
  inf_or_l, inf_or_r,
  inf_imp_l, inf_all_r,
  inf_ex_l,
  inf_all_l, inf_ex_r ctx,
  inf_whnf ]

meta def clausify_at (c : cls) (i : nat) : tactic (option (list cls)) := do
opened ← cls.open_constn c (c↣num_quants + i),
lit ← return $ cls.get_lit opened.1 0,
maybe_clausified ← first_some (do
  r ← clausification_rules (list.taken c↣num_quants opened.2),
  [r lit opened.1]),
match maybe_clausified with
| none := return none
| some clsfd := return $ some (do c' ← clsfd, [cls.close_constn c' opened.2])
end

meta def clausify_core : cls → tactic (option (list cls)) | c := do
one_step ← first_some (do i ← range c↣num_lits, [clausify_at c i]),
match one_step with
| some next := do
  next' ← sequence (do n ← next, [do
        n' ← clausify_core n,
        return $ option.get_or_else n' [n]]),
  return (some $ list.join next')
| none := return none
end

meta def clausify (cs : list cls) : tactic (list cls) :=
liftM join $ sequence (do c ← cs, [do cs' ← clausify_core c, return (option.get_or_else cs' [c])])

meta def clausification_pre : resolution_prover unit := preprocessing_rule $ λnew, do
clausified ← resolution_prover_of_tactic $ sequence (do n ← new,
           [do n' ← clausify_core n, return $ option.get_or_else n' [n]]),
return (list.join clausified)

meta def clausification_inf : inference := λgiven, do
clausified ← resolution_prover_of_tactic $ clausify_core (active_cls.c given),
match clausified with
| some cs := do forM' cs add_inferred, remove_redundant (active_cls.id given)
| none := return ()
end
