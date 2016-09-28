import prover
open tactic

-- set_option trace.resolution true

example {a b} : ¬(b ∨ ¬a) ∨ (a → b) := by prover_tactic
example {a} : a ∨ ¬a := by prover_tactic
example {a} : (a ∧ a) ∨ (¬a ∧ ¬a) := by prover_tactic
example (i : Type) (c : i) (p : i → Prop) (f : i → i) :
  p c → (∀x, p x → p (f x)) → p (f (f (f c))) := by prover_tactic

example (i : Type) (p : i → Prop) : ∀x, p x → ∃x, p x := by prover_tactic

example (i : Type) (c : i) (p : i → i → Prop) : (∀x y, p x y) → (∀x,∃z, ¬p x z) → false := by prover_tactic

example (i : Type) (c : i) (p : i → Prop) : (∀x, p x) → ¬¬∀x, p x := by prover_tactic

-- Requires non-empty domain.
example {i : Type} (c : i) (p : i → Prop) :
  (∀x y, p x ∨ p y) → (∀x y, ¬p x ∨ ¬p y) → false := by prover_tactic

example (i : Type) (a b : i) (p : i → Prop) (H : a = b) : p b → p a :=
by prover_tactic

example (i : Type) (a b : i) (p : i → Prop) (H : a = b) : p a → p b :=
by prover_tactic

example (i : Type) (a b : i) (p : i → Prop) (H : a = b) : p b = p a :=
by prover_tactic

example (i : Type) (c : i) (p : i → Prop) (f g : i → i) :
p c → (∀x, p x → p (f x)) → (∀x, p x → f x = g x) → f (f c) = g (g c) :=
by prover_tactic

example (i : Type) (p q : i → i → Prop) (a b c d : i) :
  (∀x y z, p x y ∧ p y z → p x z) →
  (∀x y z, q x y ∧ q y z → q x z) →
  (∀x y, q x y → q y x) →
  (∀x y, p x y ∨ q x y) →
  p a b ∨ q c d :=
by prover_tactic

-- This example from Davis-Putnam actually requires a non-empty domain
example (i : Type) (c : i) (f g : i → i → Prop) (z : i → i → i) :
  (∀x y, ¬((f x y → f y (z x y) ∧ f (z x y) (z x y)) ∧ (f x y ∧ g x y → g x (z x y) ∧ g (z x y) (z x y)))) -> false :=
by prover_tactic

example (person : Type) (someone : person) (drinks : person → Prop) :
  ∃canary, drinks canary → ∀other, drinks other := by prover_tactic

example {p q : ℕ → Prop} {r} : (∀x y, p x ∧ q y ∧ r) -> ∀x, (p x ∧ r ∧ q x) := by prover_tactic
