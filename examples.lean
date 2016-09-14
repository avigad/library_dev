import prover

example {a b} : ¬(b ∨ ¬a) ∨ (a → b) := by prover_tactic
example {a} : a ∨ ¬a := by prover_tactic
example {a} : (a ∧ a) ∨ (¬a ∧ ¬a) := by prover_tactic
example (i : Type) (c : i) (p : i → Prop) (f : i → i) :
  p c → (∀x, p x → p (f x)) → p (f (f (f c))) := by prover_tactic
