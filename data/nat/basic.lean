/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

Basic operations on the natural numbers.
-/
import tools.super.prover
open tactic

namespace nat

-- TODO(gabriel): can we drop addl?
/- a variant of add, defined by recursion on the first argument -/
definition addl : ℕ → ℕ → ℕ
| (succ x) y := succ (addl x y)
| 0        y := y
local infix ` ⊕ `:65 := addl

@[simp] lemma addl_zero_left (n : ℕ) : 0 ⊕ n = n := rfl
@[simp] lemma addl_succ_left (m n : ℕ) : succ m ⊕ n = succ (m ⊕ n) := rfl

@[simp] lemma zero_has_zero : nat.zero = 0 := rfl

local attribute [simp] nat.add_zero nat.add_succ nat.zero_add nat.succ_add

@[simp] theorem addl_zero_right (n : ℕ) : n ⊕ 0 = n :=
begin induction n, simp, simp [ih_1] end

@[simp] theorem addl_succ_right (n m : ℕ) : n ⊕ succ m = succ (n ⊕ m) :=
begin induction n, simp, simp [ih_1] end

@[simp] theorem add_eq_addl (x y : ℕ) : x ⊕ y = x + y :=
begin induction x, simp, simp [ih_1] end

/- successor and predecessor -/

theorem add_one_ne_zero (n : ℕ) : n + 1 ≠ 0 := succ_ne_zero _

theorem eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
begin induction n, repeat { super } end

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃k : ℕ, n = succ k :=
by super with nat.eq_zero_or_eq_succ_pred

theorem succ_inj {n m : ℕ} (H : succ n = succ m) : n = m := by super

theorem discriminate {B : Type _} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B :=
begin cases n, super, super end

lemma one_succ_zero : 1 = succ 0 := rfl
local attribute [simp] one_succ_zero

theorem two_step_induction_on {P : ℕ → Prop} (a : ℕ) (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a :=
begin assert stronger : P a ∧ P (succ a), induction a,
      repeat { super with nat.one_succ_zero } end

theorem sub_induction {P : ℕ → ℕ → Prop} (n m : ℕ) (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : P n m :=
begin assert general : ∀m, P n m,
      induction n, super with nat.one_succ_zero, intro, induction m_1,
      repeat { super with nat.one_succ_zero } end

/- addition -/

/-
Remark: we use 'local attributes' because in the end of the file
we show nat is a comm_semiring, and we will automatically inherit
the associated [simp] lemmas from algebra
-/

theorem succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m := by simp

local attribute [simp] nat.add_comm nat.add_assoc nat.add_left_comm

protected theorem add_right_comm (n m k : ℕ) : n + m + k = n + k + m := by simp

theorem eq_zero_and_eq_zero_of_add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
by super with nat.eq_zero_of_add_eq_zero_right nat.eq_zero_of_add_eq_zero_left

theorem add_one (n : ℕ) : n + 1 = succ n := rfl

-- TODO(gabriel): make add_one and one_add global simp lemmas?
local attribute [simp] add_one

theorem one_add (n : ℕ) : 1 + n = succ n := by simp

local attribute [simp] one_add

end nat

section
open nat
definition iterate {A : Type} (op : A → A) : ℕ → A → A
 | 0 := λ a, a
 | (succ k) := λ a, op (iterate k a)

notation f`^[`n`]` := iterate f n
end
