import init.meta.tactic
open expr list tactic

lemma clause_of_formula {p} : p → ¬¬p := λx y, y x

lemma and_l {a b c} : ((a ∧ b) → c) → (a → b → c) :=
λabc a b, abc (and.intro a b)

lemma and_r1 {a b c} : (¬(a ∧ b) → c) → (¬a → c) :=
λnabc na, nabc (λab, na (and.left ab))

lemma and_r2 {a b c} : (¬(a ∧ b) → c) → (¬b → c) :=
λnabc na, nabc (λab, na (and.right ab))

meta_definition clauses_of_sequent (p : expr) : tactic (list expr) :=
do c ← infer_type p, lit ← return (binding_domain c),
if is_pi c = ff then return [p]
else if is_app_of lit `and = tt ∧ get_app_num_args lit = 2 then do
  p1 ← mk_mapp `and_l [none, none, none, some p],
  clauses_of_sequent p1
else if is_app_of lit `not = tt ∧ get_app_num_args lit = 1 then
  match get_app_args lit with
  | [atom] :=
    if is_app_of atom `and = tt ∧ get_app_num_args atom = 2 then do
      p1 ← mk_mapp `and_r1 [none,none,none,some p],
      cs1 ← clauses_of_sequent p1,
      p2 ← mk_mapp `and_r2 [none,none,none,some p],
      cs2 ← clauses_of_sequent p2,
      return (cs1 ++ cs2)
    else return [p]
  | _ := return [p]
  end
else return [p]

meta_definition clausify_list : list expr → tactic (list expr)
| (proof_of_sequent :: rest) := do
    clauses ← clauses_of_sequent proof_of_sequent,
    rest_clauses ← clausify_list rest,
    return (clauses ++ rest_clauses)
 | [] := return []

meta_definition put_clauses_in_context : list expr → nat → tactic unit
| (p::ps) n :=
  do c ← infer_type p,
    assertv (mk_simple_name ("cls_" ++ to_string n)) c p,
    put_clauses_in_context ps (n+1)
| [] n := return ()

meta_definition clausifyn (hyps : list expr) : tactic unit := do
clauses ← clausify_list hyps,
foreach hyps clear,
put_clauses_in_context clauses 1

meta_definition clausify_target : tactic unit :=
do
  hyps ← intros,
  by_contr ← mk_const `classical.by_contradiction,
  apply by_contr,
  intro `target,
  hyp ← get_local `target,
  clausifyn (hyp :: hyps)

lemma test {a b} : (a ∧ b → false) → (¬(a ∧ b) → false) → false :=
by do
  clausify_target,
  trace_state,
  get_local `cls_3 >>= apply, intro1,
  get_local `cls_4 >>= apply, intro1,
  get_local `cls_2 >>= apply,
  assumption,assumption
