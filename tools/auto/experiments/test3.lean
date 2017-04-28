/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Examples from the tutorial.
-/
import ..finish
open auto

section
variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by finish
example : p ∨ q ↔ q ∨ p := by finish

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by finish
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by finish

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by finish [iff_def]
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by finish

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by finish
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by finish
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by finish
example : ¬p ∨ ¬q → ¬(p ∧ q) := by finish
example : ¬(p ∧ ¬ p) := by finish
example : p ∧ ¬q → ¬(p → q) := by finish
example : ¬p → (p → q) := by finish
example : (¬p ∨ q) → (p → q) := by finish
example : p ∨ false ↔ p := by finish
example : p ∧ false ↔ false := by finish
example : ¬(p ↔ ¬p) := by finish
example : (p → q) → (¬q → ¬p) := by finish

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by finish
example : ¬(p ∧ q) → ¬p ∨ ¬q := by finish
example : ¬(p → q) → p ∧ ¬q := by finish
example : (p → q) → (¬p ∨ q) := by finish
example : (¬q → ¬p) → (p → q) := by finish
example : p ∨ ¬p := by finish
example : (((p → q) → p) → p) := by finish
end

/- to get the ones that are sorried, we need to find an element in the environment
   to instantiate a metavariable -/

section

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop

example : (∃ x : A, r) → r := by finish
--example : r → (∃ x : A, r) := by finish
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by finish

theorem foo: (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
begin 
  simp [iff_def], 
  trace "hello",
  auto.preprocess_goal {},
  auto.preprocess_hyps {},
  trace "goodbye"
end

#exit

example (h : ∀ x, ¬ ¬ p x) : p a := by finish
example (h : ∀ x, ¬ ¬ p x) : ∀ x, p x := by finish

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by finish

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by finish
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by finish
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by finish
example : (∃ x, ¬ p x) → (¬ ∀ x, p x) := by finish
/-
example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by finish [iff_def]
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := begin safe [iff_def] end -- by finish [iff_def]
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by finish [iff_def]

example : (∃ x, p x → r) → (∀ x, p x) → r := by finish
example : (∃ x, r → p x) → (r → ∃ x, p x) := by finish
-/
end
