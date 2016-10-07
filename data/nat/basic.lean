/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

Basic operations on the natural numbers.
-/
-- import algebra.ring
import automation.super.prover
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
lemma add_zero (n : ℕ) : n + 0 = n := rfl
lemma add_succ (n m : ℕ) : n + succ m = succ (n + m) := rfl

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

@[simp] theorem pred_zero : pred 0 = 0 := rfl
@[simp] theorem pred_succ (n : ℕ) : pred (succ n) = n := rfl

theorem eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
begin induction n, repeat { super } end

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃k : ℕ, n = succ k :=
by super with nat.eq_zero_or_eq_succ_pred

theorem succ_inj {n m : ℕ} (H : succ n = succ m) : n = m := by super

theorem discriminate {B : Type _} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B :=
begin cases n, super, super end

theorem two_step_induction_on {P : ℕ → Prop} (a : ℕ) (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a :=
begin assert stronger : P a ∧ P (succ a), induction a, repeat { super } end

theorem sub_induction {P : ℕ → ℕ → Prop} (n m : ℕ) (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : P n m :=
begin assert general : ∀m, P n m,
      induction n, super, intro, induction m_1, super, super, super end

/- addition -/

/-
Remark: we use 'local attributes' because in the end of the file
we show not is a comm_semiring, and we will automatically inherit
the associated [simp] lemmas from algebra
-/

theorem succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m := by simp

-- TODO(gabriel): shouldn't this simplify the other way around to be consistent with the notation?
protected theorem add_assoc (n m k : ℕ) : (n + m) + k = n + (m + k) :=
begin induction k, simp, simp [ih_1] end

-- TODO(gabriel): add some AC handling to super
protected theorem add_left_comm (n m k : ℕ) : n + (m + k) = m + (n + k) :=
begin repeat { rw (@nat.add_comm n _) }, simp [nat.add_assoc] end

local attribute [simp] nat.add_comm nat.add_assoc nat.add_left_comm

protected theorem add_right_comm (n m k : ℕ) : n + m + k = n + k + m := by simp

protected theorem add_left_cancel {n m k : ℕ} : n + m = n + k → m = k :=
begin induction n, super, super end

protected theorem add_right_cancel {n m k : ℕ} (H : n + m = k + m) : n = k :=
by super with nat.add_comm nat.add_left_cancel

theorem eq_zero_of_add_eq_zero_right {n m : ℕ} : n + m = 0 → n = 0 :=
begin cases n, super, super end

theorem eq_zero_of_add_eq_zero_left {n m : ℕ} (H : n + m = 0) : m = 0 :=
by super with nat.eq_zero_of_add_eq_zero_right

theorem eq_zero_and_eq_zero_of_add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
by super with nat.eq_zero_of_add_eq_zero_right nat.eq_zero_of_add_eq_zero_left

theorem add_one (n : ℕ) : n + 1 = succ n := rfl

-- TODO(gabriel): make add_one and one_add global simp lemmas?
local attribute [simp] add_one

theorem one_add (n : ℕ) : 1 + n = succ n := by simp

local attribute [simp] one_add

theorem succ_eq_add_one (n : ℕ) : succ n = n + 1 :=
rfl

/- multiplication -/

protected theorem mul_zero (n : ℕ) : n * 0 = 0 :=
rfl

theorem mul_succ (n m : ℕ) : n * succ m = n * m + n :=
rfl

local attribute [simp] nat.mul_zero nat.mul_succ

-- commutativity, distributivity, associativity, identity

protected theorem zero_mul (n : ℕ) : 0 * n = 0 :=
begin induction n, simp, simp [ih_1] end

theorem succ_mul (n m : ℕ) : (succ n) * m = (n * m) + m :=
begin induction m, simp, simp [ih_1] end

local attribute [simp] nat.zero_mul nat.succ_mul

protected theorem mul_comm (n m : ℕ) : n * m = m * n :=
begin induction n, simp, simp [ih_1] end

protected theorem right_distrib (n m k : ℕ) : (n + m) * k = n * k + m * k :=
begin induction k, simp, simp [ih_1] end

local attribute [simp] nat.mul_comm nat.right_distrib

protected theorem left_distrib (n m k : ℕ) : n * (m + k) = n * m + n * k :=
begin rewrite nat.mul_comm, simp end

local attribute [simp] nat.left_distrib

protected theorem mul_assoc (n m k : ℕ) : (n * m) * k = n * (m * k) :=
begin induction k, simp, simp [ih_1] without nat.mul_comm end

local attribute [simp] nat.mul_assoc

lemma one_succ_zero : 1 = succ 0 := rfl
local attribute [simp] one_succ_zero

protected theorem mul_one (n : ℕ) : n * 1 = n := by simp
local attribute [simp] nat.mul_one

protected theorem one_mul (n : ℕ) : 1 * n = n := by simp
local attribute [simp] nat.one_mul

theorem eq_zero_or_eq_zero_of_mul_eq_zero {n m : ℕ} : n * m = 0 → n = 0 ∨ m = 0 :=
begin cases n, super, cases m, super, super end

-- TODO(gabriel): port rings
-- attribute [instance]
-- protected definition comm_semiring : comm_semiring nat :=
-- ⦃comm_semiring,
--  add            := nat.add,
--  add_assoc      := nat.add_assoc,
--  zero           := nat.zero,
--  zero_add       := nat.zero_add,
--  add_zero       := nat.add_zero,
--  add_comm       := nat.add_comm,
--  mul            := nat.mul,
--  mul_assoc      := nat.mul_assoc,
--  one            := nat.succ nat.zero,
--  one_mul        := nat.one_mul,
--  mul_one        := nat.mul_one,
--  left_distrib   := nat.left_distrib,
--  right_distrib  := nat.right_distrib,
--  zero_mul       := nat.zero_mul,
--  mul_zero       := nat.mul_zero,
--  mul_comm       := nat.mul_comm⦄

end nat

section
open nat
definition iterate {A : Type} (op : A → A) : ℕ → A → A
 | 0 := λ a, a
 | (succ k) := λ a, op (iterate k a)

notation f`^[`n`]` := iterate f n
end
