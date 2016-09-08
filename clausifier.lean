import init.meta.tactic
open expr list tactic monad decidable

lemma clause_of_formula {p} : p → ¬¬p := λx y, y x

lemma false_r {c} : (¬false → c) → c := λnfc, nfc (λx, x)
lemma true_l {c} : (true → c) → c := λtc, tc true.intro

lemma not_r {a c} : (¬¬a → c) → (a → c) := λnnac a, nnac (clause_of_formula a)

lemma and_l {a b c} : ((a ∧ b) → c) → (a → b → c) := λabc a b, abc (and.intro a b)
lemma and_r1 {a b c} : (¬(a ∧ b) → c) → (¬a → c) := λnabc na, nabc (λab, na (and.left ab))
lemma and_r2 {a b c} : (¬(a ∧ b) → c) → (¬b → c) := λnabc na, nabc (λab, na (and.right ab))

lemma or_l1 {a b c} : ((a ∨ b) → c) → (a → c) := λabc a, abc (or.inl a)
lemma or_l2 {a b c} : ((a ∨ b) → c) → (b → c) := λabc b, abc (or.inr b)
lemma or_r {a b c} : (¬(a ∨ b) → c) → (¬a → ¬b → c) := λnabc na nb, nabc (λab, or.elim ab na nb)

lemma imp_l1 {a b c} : ((a → b) → c) → (¬a → c) := λabc na, abc (λa, absurd a na)
lemma imp_l2 {a b c} : ((a → b) → c) → (b → c) := λabc b, abc (λa, b)
lemma imp_r {a b c} : (¬(a → b) → c) → (a → ¬b → c) := λnabc a nb, nabc (λab, absurd (ab a) nb)

meta_definition try_rules
  (pred : expr → bool)
  (rules : list (tactic expr))
  (p atom : expr) : tactic (option (list expr)) :=
if pred atom = ff then return none else do
ps ← @sequence tactic _ _ rules,
return (some ps)

meta_definition try_rules_bin (pred : expr → bool) (rules : list name) (p atom : expr) :
  tactic (option (list expr)) :=
try_rules pred (map (λrn, mk_mapp rn [none, none, none, some p]) rules) p atom

meta_definition is_not_const (e : expr) : bool := to_bool (is_not e ≠ none)
meta_definition try_not_r (p atom : expr) : tactic (option (list expr)) :=
try_rules is_not_const [mk_mapp ``not_r [none, none, some p]] p atom

meta_definition try_false_l (p atom : expr) : tactic (option (list expr)) :=
try_rules is_false [] p atom
meta_definition try_false_r (p atom : expr) : tactic (option (list expr)) :=
try_rules is_false [mk_mapp ``false_r [none, some p]] p atom

meta_definition is_true_const (e : expr) : bool := to_bool (is_constant_of e ``true = tt)
meta_definition try_true_l (p atom : expr) : tactic (option (list expr)) :=
try_rules is_false [mk_mapp ``true_l [none, some p]] p atom
meta_definition try_true_r (p atom : expr) : tactic (option (list expr)) :=
try_rules is_false [] p atom

meta_definition is_and (e : expr) : bool := to_bool (is_app_of e ``and = tt ∧ get_app_num_args e = 2)
meta_definition try_and_l : expr → expr → tactic (option (list expr)) := try_rules_bin is_and [``and_l]
meta_definition try_and_r : expr → expr → tactic (option (list expr)) := try_rules_bin is_and [``and_r1, ``and_r2]

meta_definition is_or (e : expr) : bool := to_bool (is_app_of e ``or = tt ∧ get_app_num_args e = 2)
meta_definition try_or_l : expr → expr → tactic (option (list expr)) := try_rules_bin is_or [``or_l1, ``or_l2]
meta_definition try_or_r : expr → expr → tactic (option (list expr)) := try_rules_bin is_or [``or_r]

meta_definition is_imp (e : expr) : bool := to_bool (is_pi e = tt ∧ has_var e = ff)
meta_definition try_imp_l : expr → expr → tactic (option (list expr)) := try_rules_bin is_imp [``imp_l1, ``imp_l2]
meta_definition try_imp_r : expr → expr → tactic (option (list expr)) := try_rules_bin is_imp [``imp_r]

meta_definition first_some {a} : list (tactic (option a)) → tactic (option a)
| [] := return none
| (x::xs) := do xres ← x, match xres with some y := return (some y) | none := first_some xs end

inductive clause_info
| cons : expr → expr → expr → clause_info
| tail : expr → clause_info

meta_definition clause_info_of_proof (p : expr) : tactic clause_info :=
do c ← infer_type p,
fls ← mk_const ``false,
match is_not c with
| some hd := do
    n ← mk_fresh_name,
    b ← return $ local_const n n binder_info.default hd,
    return (clause_info.cons b hd (app p b))
| none := if is_pi c = tt
  then do
    n ← mk_fresh_name,
    b ← return $ local_const n (binding_name c) (binding_info c) (binding_domain c),
    return (clause_info.cons b (binding_domain c) (app p b))
  else return (clause_info.tail c)
end

meta_definition lambda_local_const (lc e : expr) : expr :=
match lc with
| local_const uniq pp info t := lam pp info t (abstract_local e uniq)
| _ := lambda_local_const e lc
end

meta_definition clauses_of_sequent (p : expr) : tactic (list expr) :=
do clsinfo ← clause_info_of_proof p, match clsinfo with
| clause_info.cons b lit rest := do
  rule_applicable_to_head ← match is_not lit with
  | some atom := first_some [try_false_r p atom, try_true_r p atom, try_not_r p atom, try_and_r p atom, try_or_r p atom, try_imp_r p atom]
  | none := first_some [try_false_l p lit, try_true_l p lit, try_and_l p lit, try_or_l p lit, try_imp_l p lit]
  end,
  match rule_applicable_to_head with
  | some new_ps := do
      new_ps2 ← @mapM tactic _ _ _ clauses_of_sequent new_ps,
      return (join new_ps2)
  | none := do
      new_rests ← clauses_of_sequent rest,
      return (map (lambda_local_const b) new_rests)
  end
| clause_info.tail t := return [p]
end

meta_definition clausify_list (ps : list expr) : tactic (list expr) :=
do clause_lists ← @mapM tactic _ _ _ clauses_of_sequent ps, return (join clause_lists)

meta_definition put_clauses_in_context : list expr → nat → tactic unit
| (p::ps) n :=
  do c ← infer_type p,
    assertv (mk_simple_name ("cls_" ++ to_string n)) c p,
    put_clauses_in_context ps (n+1)
| [] n := return ()

meta_definition clause_expr_of_formula (e : expr) : tactic expr :=
mk_mapp ``clause_of_formula [none, some e]

meta_definition clausifyn (hyps : list expr) : tactic unit := do
hyps' ← @mapM tactic _ _ _ clause_expr_of_formula hyps,
clauses ← clausify_list hyps',
foreach hyps clear,
put_clauses_in_context clauses 1

meta_definition clausify_target : tactic unit :=
do
  hyps ← intros,
  tgt ← target,
  by_contr ← mk_mapp `classical.by_contradiction [some tgt],
  apply by_contr,
  intro `target,
  hyp ← get_local `target,
  clausifyn (hyp :: hyps)

example {a b} : ((a ∨ false) ∧ b → false) → (¬a ∨ ¬b → false) → false :=
by do
  clausify_target,
  trace_state,
  get_local `cls_2 >>= apply, intro1,
  get_local `cls_3 >>= apply, intro1,
  get_local `cls_1 >>= apply,
  assumption,assumption

example {a b} : ¬(¬a ∨ b) ∨ (a → b) :=
by do clausify_target,
  trace_state,
  get_local `cls_2 >>= apply, intro1,
  get_local `cls_1 >>= apply,
  assumption, assumption
