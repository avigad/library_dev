import tools.super.clausifier tools.super.cdcl tools.super.trim
open tactic super expr monad

-- Intuitionistic propositional prover based on
-- SAT Modulo Intuitionistic Implications, Claessen and Rosen, LPAR 2015

namespace intuit

meta def check_model (intuit : tactic unit) : cdcl.solver (option cdcl.proof_term) :=
do s ← state_t.read, monad_lift $ do
hyps ← return $ s^.trail^.for (λe, e^.hyp),
subgoal ← mk_meta_var s^.local_false,
goals ← get_goals,
set_goals [subgoal],
for' s^.trail (λe,
  if e^.phase then do
    name ← get_unused_name `model (some 1),
    assertv name e^.hyp^.local_type e^.hyp
  else
    return ()),
is_solved ← first (do
  e ← s^.trail,
  guard ¬e^.phase,
  guard e^.var^.is_pi,
  a ← option.to_monad $ s^.vars^.find e^.var^.binding_domain,
  b ← option.to_monad $ s^.vars^.find e^.var^.binding_body,
  guard $ a^.phase = ff ∧ b^.phase = ff,
  return $ do
    apply e^.hyp,
    intuit,
    done, return tt) <|> return ff,
set_goals goals,
if is_solved then do
  proof ← instantiate_mvars subgoal,
  proof' ← trim proof, -- gets rid of the unnecessary asserts
  return $ some proof'
else
  return none

lemma imp1 {F a b} : b → ((a → b) → F) → F := λhb habf, habf (λha, hb)
lemma imp2 {a b} : a → (a → b) → b := λha hab, hab ha

meta def solve : unit → tactic unit | () := with_trim $ do
as_refutation,
local_false ← target, clauses ← clauses_of_context,
clauses ← get_clauses_intuit clauses,
vars ← return $ list.nub (do c ← clauses, l ← c^.get_lits, [l^.formula]),
imp_axs ← sequence (do
  v ← vars, guard v^.is_pi,
  a ← return v^.binding_domain, b ← return v^.binding_body,
  pr ← [mk_mapp ``intuit.imp1 [some local_false, some a, some b],
        mk_mapp ``intuit.imp2 [some a, some b]],
  [pr >>= clause.of_proof local_false]),
clauses ← return $ imp_axs ++ clauses,
result ← cdcl.solve (check_model (solve ())) local_false clauses,
match result with
| (cdcl.result.sat interp) :=
  let interp' := do e ← interp^.to_list, [if e^.2 = tt then e^.1 else (`(not)) e^.1] in
  do pp_interp ← pp interp',
     fail (to_fmt "satisfying assignment: " ++ pp_interp)
| (cdcl.result.unsat proof) := exact proof
end

end intuit

meta def intuit : tactic unit := _root_.intuit.solve ()

example (a b) : a → (a → b) → b := by intuit
example (a b c) : (a → c) → (c → b) → ((a → b) → a) → a := by intuit
example (a b) : a ∨ ¬a → ((a → b) → a) → a := by intuit

def compose {a b c} : (a → b) → (b → c) → (a → c) := by intuit
