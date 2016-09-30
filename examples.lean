import prover
open tactic

-- set_option trace.resolution true

namespace tactic.interactive
meta def with_lemma (n : types.ident) : tactic unit := do
p ← mk_mapp n [],
t ← infer_type p,
n' ← get_unused_name n none,
assertv n' t p
end tactic.interactive

example : ∀x y : ℕ, x + y = y + x :=
begin with_lemma nat.succ_add, with_lemma nat.zero_add, intros, induction x, repeat prover_tactic end

example {a b} : ¬(b ∨ ¬a) ∨ (a → b) := by prover_tactic
example {a} : a ∨ ¬a := by prover_tactic
example {a} : (a ∧ a) ∨ (¬a ∧ ¬a) := by prover_tactic
example (i : Type) (c : i) (p : i → Prop) (f : i → i) :
  p c → (∀x, p x → p (f x)) → p (f (f (f c))) := by prover_tactic

example (i : Type) (p : i → Prop) : ∀x, p x → ∃x, p x := by prover_tactic

example (i : Type) (c : i) (p : i → i → Prop) : (∀x y, p x y) → ∃x, ∀z, p x z := by prover_tactic

example (i : Type) (c : i) (p : i → Prop) : (∀x, p x) → ¬¬∀x, p x := by prover_tactic

-- Requires non-empty domain.
example {i : Type} (c : i) (p : i → Prop) :
  (∀x y, p x ∨ p y) → ∃x y, p x ∧ p y := by prover_tactic

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
example (i : Type) (c : i) (f g : i → i → Prop) :
  ∃x y, ∀z, (f x y → f y z ∧ f z z) ∧ (f x y ∧ g x y → g x z ∧ g z z) :=
by prover_tactic

example (person : Type) (someone : person) (drinks : person → Prop) :
  ∃canary, drinks canary → ∀other, drinks other := by prover_tactic

example {p q : ℕ → Prop} {r} : (∀x y, p x ∧ q y ∧ r) -> ∀x, (p x ∧ r ∧ q x) := by prover_tactic
