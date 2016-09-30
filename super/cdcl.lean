import clause clausifier cdcl_solver
open tactic expr monad

private meta def theory_solver_of_tactic (th_solver : tactic unit) : cdcl.solver (option cdcl.proof_term) :=
do s ← stateT.read, ↑do
hyps ← return $ s↣trail↣for (λe, e↣hyp),
subgoal ← mk_meta_var (const ``false []),
goals ← get_goals,
set_goals [subgoal],
hvs ← forM hyps (λhyp, assertv hyp↣local_pp_name hyp↣local_type hyp),
solved ← (do th_solver, now, return tt) <|> return ff,
set_goals goals,
if solved then do
  proof ← instantiate_mvars subgoal,
  proof' ← whnf proof, -- gets rid of the unnecessary asserts
  return $ some proof'
else
  return none

meta def cdcl_t (th_solver : tactic unit) : tactic unit := do
intros,
target_name ← get_unused_name `target none, tgt ← target,
mk_mapp ``classical.by_contradiction [some tgt] >>= apply, intro target_name,
hyps ← local_context,
gen_clauses ← mapM clause.of_proof hyps,
clauses ← clausify gen_clauses,
res ← cdcl.solve (theory_solver_of_tactic th_solver) clauses,
match res with
| (cdcl.result.unsat proof) := exact proof
| (cdcl.result.sat interp) :=
  let interp' := do e ← interp↣to_list, [cdcl.formula_of_lit e↣1 e↣2] in
  do pp_interp ← pp interp',
     fail (to_fmt "satisfying assignment: " ++ pp_interp)
end

meta def cdcl : tactic unit := cdcl_t skip

example {a} : a → ¬a → false := by cdcl
example {a} : a ∨ ¬a := by cdcl
example {a} {b : Prop} : a → (a → b) → b := by cdcl
example {a b c} : (a → b) → (¬a → b) → (b → c) → b ∧ c := by cdcl

private meta def lit_unification : tactic unit :=
do ls ← local_context, first $ do l ← ls, [do apply l, assumption]
example {p : ℕ → Prop} : p 2 ∨ p 4 → (p (2*2) → p (2+0)) → p (1+1) :=
by cdcl_t lit_unification

example {p : ℕ → Prop} :
        list.foldl (λf v, f ∧ (v ∨ ¬v)) true (map p (list.range 5)) :=
by cdcl
