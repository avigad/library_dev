/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

Basic operations on the natural numbers.
-/
-- import algebra.ring
import super.prover
open tactic

namespace nat

/- a variant of add, defined by recursion on the first argument -/
definition addl : ℕ → ℕ → ℕ
| (succ x) y := succ (addl x y)
| 0        y := y
local infix ` ⊕ `:65 := addl

-- TODO(gabriel): integrate function definitions in super
lemma addl_zero_left (n : ℕ) : 0 ⊕ n = n := rfl
lemma addl_succ_left (m n : ℕ) : succ m ⊕ n = succ (m ⊕ n) := rfl
lemma add_zero (n : ℕ) : n + 0 = n := rfl
lemma add_succ (n m : ℕ) : n + succ m = succ (n + m) := rfl

theorem addl_zero_right (n : ℕ) : n ⊕ 0 = n :=
begin induction n, apply rfl, super with nat.addl_succ_left end

theorem addl_succ_right (n m : ℕ) : n ⊕ succ m = succ (n ⊕ m) :=
begin induction n, apply rfl, apply (congr_arg succ v_0) end

theorem add_eq_addl (x y : ℕ) : x + y = x ⊕ y :=
begin induction x,
      repeat { super with nat.addl_zero_left nat.addl_succ_left
                          nat.zero_add nat.succ_add } end

/- successor and predecessor -/

@[simp] theorem add_one_ne_zero (n : ℕ) : n + 1 ≠ 0 := succ_ne_zero _

@[simp] theorem pred_zero : pred 0 = 0 := rfl
@[simp] theorem pred_succ (n : ℕ) : pred (succ n) = n := rfl

theorem eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
begin induction n, super, super with nat.pred_succ end

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃k : ℕ, n = succ k :=
by super with nat.eq_zero_or_eq_succ_pred

theorem succ_inj {n m : ℕ} (H : succ n = succ m) : n = m :=
by super with nat.pred_succ

theorem discriminate {B : Prop} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B :=
begin induction n, super, super end

theorem two_step_induction_on {P : ℕ → Prop} (a : ℕ) (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a :=
have stronger : P a ∧ P (succ a), from
  nat.induction_on a
    (and.intro H1 H2)
    (take k IH,
      have IH1 : P k, from and.elim_left IH,
      have IH2 : P (succ k), from and.elim_right IH,
        and.intro IH2 (H3 k IH1 IH2)),
  and.elim_left stronger

theorem sub_induction {P : ℕ → ℕ → Prop} (n m : ℕ) (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : P n m :=
have general : ∀m, P n m, from nat.induction_on n H1
  (take k : ℕ,
    assume IH : ∀m, P k m,
    take m : ℕ,
    nat.cases_on m (H2 k) (take l, (H3 k l (IH l)))),
general m

/- addition -/

/-
Remark: we use 'local attributes' because in the end of the file
we show not is a comm_semiring, and we will automatically inherit
the associated [simp] lemmas from algebra
-/
local attribute [simp] nat.add_zero nat.add_succ
local attribute [simp] nat.zero_add nat.succ_add

theorem succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m :=
begin super with nat.add_succ nat.succ_add nat.add_comm end

protected theorem add_assoc (n m k : ℕ) : (n + m) + k = n + (m + k) :=
begin induction k, super with nat.add_zero, super with nat.add_succ end

protected theorem add_left_comm : Π (n m k : ℕ), n + (m + k) = m + (n + k) :=
begin with_lemmas nat.add_assoc nat.add_comm, super end

local attribute [simp] nat.add_comm nat.add_assoc nat.add_left_comm

protected theorem add_right_comm : Π (n m k : ℕ), n + m + k = n + k + m :=
begin super with nat.add_assoc nat.add_comm end

-- TODO(gabriel): how to deal with 0 and 0 in super?
lemma zero_has_zero : nat.zero = 0 := rfl
lemma nat_zero_add (x : ℕ) : nat.zero + x = x := nat.zero_add _

protected theorem add_left_cancel {n m k : ℕ} : n + m = n + k → m = k :=
begin induction n, super with nat.zero_add nat.nat_zero_add,
                   super with nat.succ_add nat.succ_inj end

protected theorem add_right_cancel {n m k : ℕ} (H : n + m = k + m) : n = k :=
by super with nat.add_comm nat.add_left_cancel

theorem eq_zero_of_add_eq_zero_right {n m : ℕ} : n + m = 0 → n = 0 :=
begin cases n, super, super with nat.succ_ne_zero nat.succ_add end

theorem eq_zero_of_add_eq_zero_left {n m : ℕ} (H : n + m = 0) : m = 0 :=
eq_zero_of_add_eq_zero_right (eq.trans (nat.add_comm m n) H)

theorem eq_zero_and_eq_zero_of_add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
and.intro (eq_zero_of_add_eq_zero_right H) (eq_zero_of_add_eq_zero_left H)

theorem add_one (n : ℕ) : n + 1 = succ n := rfl

-- local attribute [simp] add_one

theorem one_add (n : ℕ) : 1 + n = succ n :=
by super with nat.add_comm nat.add_one

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
begin induction n, super with nat.mul_zero, super with nat.mul_succ nat.add_zero end

theorem succ_mul (n m : ℕ) : (succ n) * m = (n * m) + m :=
begin induction m, super with nat.mul_zero, simp, super with nat.add_assoc nat.add_comm end

local attribute [simp] nat.zero_mul nat.succ_mul

protected theorem mul_comm (n m : ℕ) : n * m = m * n :=
begin induction n, super with nat.mul_zero nat.zero_mul, super with nat.mul_succ nat.succ_mul end

protected theorem right_distrib (n m k : ℕ) : (n + m) * k = n * k + m * k :=
begin induction k, super with nat.mul_zero, simp, super end

protected theorem left_distrib (n m k : ℕ) : n * (m + k) = n * m + n * k :=
begin rewrite nat.mul_comm, rewrite nat.right_distrib, super with nat.mul_comm end

local attribute [simp] nat.right_distrib nat.left_distrib

protected theorem mul_assoc (n m k : ℕ) : (n * m) * k = n * (m * k) :=
begin induction k, super with nat.mul_zero, simp, super end

local attribute [simp] nat.mul_assoc

-- FIXME(gabriel)
lemma one_succ_zero : 1 = succ 0 := rfl

protected theorem mul_one (n : ℕ) : n * 1 = n :=
by super with nat.one_succ_zero nat.mul_succ nat.mul_zero nat.zero_add

local attribute [simp] nat.mul_one

protected theorem one_mul (n : ℕ) : 1 * n = n :=
by super with nat.mul_one nat.mul_comm

local attribute [simp] nat.one_mul

theorem eq_zero_or_eq_zero_of_mul_eq_zero {n m : ℕ} : n * m = 0 → n = 0 ∨ m = 0 :=
begin cases n, super, cases m, super, simp, super with nat.succ_ne_zero end

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
