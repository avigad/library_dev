/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
import ..nat.sub
open nat

-- TODO: where to put these?
meta def simp_coe_attr : user_attribute :=
{ name     := `simp.coe,
  descr    := "rules for pushing coercions inwards"}

run_command attribute.register ``simp_coe_attr

meta def simp_coe_out_attr : user_attribute :=
{ name     := `simp.coe_out,
  descr    := "rules for pushing coercions outwards"}

run_command attribute.register ``simp_coe_out_attr


/- the type, coercions, and notation -/

inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int

notation `ℤ` := int

instance : has_coe nat int := ⟨int.of_nat⟩

notation `-[1+ ` n `]` := int.neg_succ_of_nat n

instance : decidable_eq int :=
by tactic.mk_dec_eq_instance

namespace int

protected theorem coe_nat_eq (n : ℕ) : ↑n = int.of_nat n := rfl

protected def zero : ℤ := of_nat 0
protected def one  : ℤ := of_nat 1

instance : has_zero ℤ := ⟨int.zero⟩
instance : has_one ℤ := ⟨int.one⟩

theorem of_nat_zero : of_nat (0 : nat) = (0 : int) := rfl

theorem of_nat_one : of_nat (1 : nat) = (1 : int) := rfl

/- definitions of basic functions -/

def neg_of_nat : ℕ → ℤ
| 0        := 0
| (succ m) := -[1+ m]

def sub_nat_nat (m n : ℕ) : ℤ :=
match (n - m : nat) with
| 0        := of_nat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k
end

private theorem sub_nat_nat_of_sub_eq_zero {m n : ℕ} (h : n - m = 0) :
  sub_nat_nat m n = of_nat (m - n) :=
begin unfold sub_nat_nat, rw [h, sub_nat_nat._match_1.equations.eqn_1] end

private theorem sub_nat_nat_of_sub_eq_succ {m n k : ℕ} (h : n - m = succ k) :
  sub_nat_nat m n = -[1+ k] :=
begin unfold sub_nat_nat, rw [h, sub_nat_nat._match_1.equations.eqn_2] end

protected def neg : ℤ → ℤ
| (of_nat n) := neg_of_nat n
| -[1+ n]    := succ n

protected def add : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m + n)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m]    (of_nat n) := sub_nat_nat n (succ m)
| -[1+ m]    -[1+ n]    := -[1+ succ (m + n)]

protected def mul : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m * n)
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m]    (of_nat n) := neg_of_nat (succ m * n)
| -[1+ m]    -[1+ n]    := of_nat (succ m * succ n)

instance : has_neg ℤ := ⟨int.neg⟩
instance : has_add ℤ := ⟨int.add⟩
instance : has_mul ℤ := ⟨int.mul⟩

theorem of_nat_add (n m : ℕ) : of_nat (n + m) = of_nat n + of_nat m := rfl
theorem of_nat_mul (n m : ℕ) : of_nat (n * m) = of_nat n * of_nat m := rfl
theorem of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 := rfl

theorem neg_of_nat_zero : -(of_nat 0) = 0 := rfl
theorem neg_of_nat_of_succ (n : ℕ) : -(of_nat (succ n)) = -[1+ n] := rfl
theorem neg_neg_of_nat_succ (n : ℕ) : -(-[1+ n]) = of_nat (succ n) := rfl

theorem of_nat_eq_coe (n : ℕ) : of_nat n = ↑n := rfl
theorem neg_succ_of_nat_coe (n : ℕ) : -[1+ n] = -↑(n + 1) := rfl

@[simp.coe] protected theorem coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n := rfl
@[simp.coe] protected theorem coe_nat_mul (m n : ℕ) : (↑(m * n) : ℤ) = ↑m * ↑n := rfl
@[simp.coe] protected theorem coe_nat_zero : ↑(0 : ℕ) = (0 : ℤ) := rfl
@[simp.coe] protected theorem coe_nat_one : ↑(1 : ℕ) = (1 : ℤ) := rfl
@[simp.coe] protected theorem coe_nat_succ (n : ℕ) : (↑(succ n) : ℤ) = ↑n + 1 := rfl

@[simp.coe_out] protected theorem coe_nat_add_out (m n : ℕ) : ↑m + ↑n = (m + n : ℤ) := rfl
@[simp.coe_out] protected theorem coe_nat_mul_out (m n : ℕ) : ↑m * ↑n = (↑(m * n) : ℤ) := rfl
@[simp.coe_out] protected theorem coe_nat_add_one_out (n : ℕ) : ↑n + (1 : ℤ) = ↑(succ n) := rfl

/- these are only for internal use -/

private theorem of_nat_add_of_nat (m n : nat) : of_nat m + of_nat n = of_nat (m + n) := rfl
private theorem of_nat_add_neg_succ_of_nat (m n : nat) :
                of_nat m + -[1+ n] = sub_nat_nat m (succ n) := rfl
private theorem neg_succ_of_nat_add_of_nat (m n : nat) :
                -[1+ m] + of_nat n = sub_nat_nat n (succ m) := rfl
private theorem neg_succ_of_nat_add_neg_succ_of_nat (m n : nat) :
                -[1+ m] + -[1+ n] = -[1+ succ (m + n)] := rfl

private theorem of_nat_mul_of_nat   (m n : nat) : of_nat m * of_nat n = of_nat (m * n) := rfl
private theorem of_nat_mul_neg_succ_of_nat (m n : nat) :
                of_nat m * -[1+ n] = neg_of_nat (m * succ n) := rfl
private theorem neg_succ_of_nat_of_nat (m n : nat) :
                -[1+ m] * of_nat n = neg_of_nat (succ m * n) := rfl
private theorem mul_neg_succ_of_nat_neg_succ_of_nat (m n : nat) :
               -[1+ m] * -[1+ n] = of_nat (succ m * succ n) := rfl

local attribute [simp] of_nat_add_of_nat of_nat_mul_of_nat neg_of_nat_zero neg_of_nat_of_succ
  neg_neg_of_nat_succ of_nat_add_neg_succ_of_nat neg_succ_of_nat_add_of_nat
  neg_succ_of_nat_add_neg_succ_of_nat of_nat_mul_neg_succ_of_nat neg_succ_of_nat_of_nat
  mul_neg_succ_of_nat_neg_succ_of_nat

/- some basic functions and properties -/

theorem of_nat.inj {m n : ℕ} (h : of_nat m = of_nat n) : m = n :=
int.no_confusion h id

protected theorem coe_nat.inj {m n : ℕ} (h : ↑m = ↑n) : m = n :=
of_nat.inj h

theorem of_nat_eq_of_nat_iff (m n : ℕ) : of_nat m = of_nat n ↔ m = n :=
iff.intro of_nat.inj (congr_arg _)

protected theorem coe_nat_eq_coe_nat_iff (m n : ℕ) : (↑m : ℤ) = ↑n ↔ m = n :=
of_nat_eq_of_nat_iff m n

theorem neg_succ_of_nat.inj {m n : ℕ} (h : neg_succ_of_nat m = neg_succ_of_nat n) : m = n :=
int.no_confusion h id

theorem neg_succ_of_nat_eq (n : ℕ) : -[1+ n] = -(n + 1) := rfl

private theorem sub_nat_nat_of_ge {m n : ℕ} (h : m ≥ n) : sub_nat_nat m n = of_nat (m - n) :=
sub_nat_nat_of_sub_eq_zero (sub_eq_zero_of_le h)

private theorem sub_nat_nat_of_lt {m n : ℕ} (h : m < n) : sub_nat_nat m n = -[1+ pred (n - m)] :=
have n - m = succ (pred (n - m)), from eq.symm (succ_pred_eq_of_pos (nat.sub_pos_of_lt h)),
by rewrite sub_nat_nat_of_sub_eq_succ this

def nat_abs (a : ℤ) : ℕ := int.cases_on a id succ

theorem nat_abs_of_nat (n : ℕ) : nat_abs n = n := rfl

theorem eq_zero_of_nat_abs_eq_zero : Π {a : ℤ}, nat_abs a = 0 → a = 0
| (of_nat m) H := congr_arg of_nat H
| -[1+ m']   H := absurd H (succ_ne_zero _)

theorem nat_abs_zero : nat_abs (0 : int) = (0 : nat) := rfl

theorem nat_abs_one : nat_abs (1 : int) = (1 : nat) := rfl

/-
   int is a ring
-/

/- addition -/

protected theorem add_comm : ∀ a b : ℤ, a + b = b + a
| (of_nat n) (of_nat m) := by simp
| (of_nat n) -[1+ m]    := rfl
| -[1+ n]    (of_nat m) := rfl
| -[1+ n]    -[1+m]     := by simp

protected theorem add_zero : ∀ a : ℤ, a + 0 = a
| (of_nat n) := rfl
| -[1+ n]   := rfl

protected theorem zero_add (a : ℤ) : 0 + a = a :=
int.add_comm a 0 ▸ int.add_zero a

private theorem sub_nat_nat_add_add (m n k : ℕ) : sub_nat_nat (m + k) (n + k) = sub_nat_nat m n :=
or.elim (le_or_gt n m)
  (assume h : n ≤ m,
    have n + k ≤ m + k, from nat.add_le_add_right h k,
    by simp [sub_nat_nat_of_ge h, sub_nat_nat_of_ge this])
  (assume h : n > m,
    have n + k > m + k, from nat.add_lt_add_right h k,
    by simp [sub_nat_nat_of_lt h, sub_nat_nat_of_lt this])

private theorem sub_nat_nat_sub {m n : ℕ} (h : m ≥ n) (k : ℕ) :
  sub_nat_nat (m - n) k = sub_nat_nat m (k + n) :=
calc
  sub_nat_nat (m - n) k = sub_nat_nat (m - n + n) (k + n) : by rewrite sub_nat_nat_add_add
                    ... = sub_nat_nat m (k + n)           : by rewrite [nat.sub_add_cancel h]

private theorem sub_nat_nat_add (m n k : ℕ) : sub_nat_nat (m + n) k = of_nat m + sub_nat_nat n k :=
begin
  note h := le_or_gt k n,
  cases h with h' h',
  { rw [sub_nat_nat_of_ge h'],
    assert h₂ : k ≤ m + n, exact (le_trans h' (le_add_left _ _)),
    rw [sub_nat_nat_of_ge h₂], simp,
    rw nat.add_sub_assoc h' },
  rw [sub_nat_nat_of_lt h'], simp, rw [succ_pred_eq_of_pos (nat.sub_pos_of_lt h')],
  transitivity, rw [-nat.sub_add_cancel (le_of_lt h')],
  apply sub_nat_nat_add_add
end

private theorem sub_nat_nat_add_neg_succ_of_nat (m n k : ℕ) :
    sub_nat_nat m n + -[1+ k] = sub_nat_nat m (n + succ k) :=
begin
  note h := le_or_gt n m,
  cases h with h' h',
  { rw [sub_nat_nat_of_ge h'], simp, rw [sub_nat_nat_sub h', add_comm] },
  assert h₂ : m < n + succ k, exact nat.lt_of_lt_of_le h' (le_add_right _ _),
  assert h₃ : m ≤ n + k, exact le_of_succ_le_succ h₂,
  rw [sub_nat_nat_of_lt h', sub_nat_nat_of_lt h₂], simp,
  rw [-add_succ, succ_pred_eq_of_pos (nat.sub_pos_of_lt h'), add_succ, succ_sub h₃, pred_succ],
  rw [add_comm n, nat.add_sub_assoc (le_of_lt h')]
end

private theorem add_assoc_aux1 (m n : ℕ) :
    ∀ c : ℤ, of_nat m + of_nat n + c = of_nat m + (of_nat n + c)
| (of_nat k) := by simp
| -[1+ k]    := by simp [sub_nat_nat_add]

private theorem add_assoc_aux2 (m n k : ℕ) :
  -[1+ m] + -[1+ n] + of_nat k = -[1+ m] + (-[1+ n] + of_nat k) :=
begin
  simp [add_succ], rw [int.add_comm, sub_nat_nat_add_neg_succ_of_nat], simp [add_succ, succ_add]
end

protected theorem add_assoc : ∀ a b c : ℤ, a + b + c = a + (b + c)
| (of_nat m) (of_nat n) c          := add_assoc_aux1 _ _ _
| (of_nat m) b          (of_nat k) := by rw [int.add_comm, -add_assoc_aux1, int.add_comm (of_nat k),
                                         add_assoc_aux1, int.add_comm b]
| a          (of_nat n) (of_nat k) := by rw [int.add_comm, int.add_comm a, -add_assoc_aux1,
                                         int.add_comm a, int.add_comm (of_nat k)]
| -[1+ m]    -[1+ n]    (of_nat k) := add_assoc_aux2 _ _ _
| -[1+ m]    (of_nat n) -[1+ k]    := by rw [int.add_comm, -add_assoc_aux2, int.add_comm (of_nat n),
                                         -add_assoc_aux2, int.add_comm -[1+ m] ]
| (of_nat m) -[1+ n]    -[1+ k]    := by rw [int.add_comm, int.add_comm (of_nat m),
                                         int.add_comm (of_nat m), -add_assoc_aux2,
                                         int.add_comm -[1+ k] ]
| -[1+ m]    -[1+ n]    -[1+ k]    := by simp [add_succ, neg_of_nat_of_succ]

/- negation -/

private theorem sub_nat_self : ∀ n, sub_nat_nat n n = 0
| 0        := rfl
| (succ m) := begin rw [sub_nat_nat_of_sub_eq_zero, nat.sub_self], rw nat.sub_self end

local attribute [simp] sub_nat_self

protected theorem add_left_inv : ∀ a : ℤ, -a + a = 0
| (of_nat 0)        := by simp
| (of_nat (succ m)) := by simp
| -[1+ m]           := by simp

/- multiplication -/

protected theorem mul_comm : ∀ a b : ℤ, a * b = b * a
| (of_nat m) (of_nat n) := by simp
| (of_nat m) -[1+ n]    := by simp
| -[1+ m]    (of_nat n) := by simp
| -[1+ m]    -[1+ n]    := by simp

private theorem of_nat_mul_neg_of_nat (m : ℕ) :
   ∀ n, of_nat m * neg_of_nat n = neg_of_nat (m * n)
| 0        := by simp
| (succ n) := by simp [neg_of_nat.equations.eqn_2]

private theorem neg_of_nat_mul_of_nat (m n : ℕ) :
    neg_of_nat m * of_nat n = neg_of_nat (m * n) :=
begin rw int.mul_comm, simp [of_nat_mul_neg_of_nat] end

private theorem neg_succ_of_nat_mul_neg_of_nat (m : ℕ) :
  ∀ n, -[1+ m] * neg_of_nat n = of_nat (succ m * n)
| 0        := by simp
| (succ n) := by simp [neg_of_nat.equations.eqn_2]

private theorem neg_of_nat_mul_neg_succ_of_nat (m n : ℕ) :
  neg_of_nat n * -[1+ m] = of_nat (n * succ m) :=
begin rw int.mul_comm, simp [neg_succ_of_nat_mul_neg_of_nat] end

local attribute [simp] of_nat_mul_neg_of_nat neg_of_nat_mul_of_nat
  neg_succ_of_nat_mul_neg_of_nat neg_of_nat_mul_neg_succ_of_nat

protected theorem mul_assoc : ∀ a b c : ℤ, a * b * c = a * (b * c)
| (of_nat m) (of_nat n) (of_nat k) := by simp
| (of_nat m) (of_nat n) -[1+ k]    := by simp
| (of_nat m) -[1+ n]    (of_nat k) := by simp
| (of_nat m) -[1+ n]   -[1+ k]     := by simp
| -[1+ m]    (of_nat n) (of_nat k) := by simp
| -[1+ m]    (of_nat n) -[1+ k]    := by simp
| -[1+ m]    -[1+ n]    (of_nat k) := by simp
| -[1+ m]    -[1+ n]   -[1+ k]     := by simp

protected theorem mul_one : ∀ (a : ℤ), a * 1 = a
| (of_nat m) := show of_nat m * of_nat 1 = of_nat m, by simp
| -[1+ m]    := show -[1+ m] * of_nat 1 = -[1+ m], by simp

protected theorem one_mul (a : ℤ) : 1 * a = a :=
int.mul_comm a 1 ▸ int.mul_one a

protected theorem mul_zero : ∀ (a : ℤ), a * 0 = 0
| (of_nat m) := begin unfold zero, simp end
| -[1+ m]    := begin unfold zero, simp end

protected theorem zero_mul (a : ℤ) : 0 * a = 0 :=
int.mul_comm a 0 ▸ int.mul_zero a

private theorem neg_of_nat_eq_sub_nat_nat_zero : ∀ n, neg_of_nat n = sub_nat_nat 0 n
| 0        := rfl
| (succ n) := rfl

private theorem of_nat_mul_sub_nat_nat (m n k : ℕ) :
  of_nat m * sub_nat_nat n k = sub_nat_nat (m * n) (m * k) :=
begin
  assert h₀ : m > 0 ∨ 0 = m,
    exact lt_or_eq_of_le (zero_le _),
  cases h₀ with h₀ h₀,
  { note h := nat.lt_or_ge n k,
    cases h with h h,
    { assert h' : m * n < m * k,
        exact nat.mul_lt_mul_of_pos_left h h₀,
      rw [sub_nat_nat_of_lt h, sub_nat_nat_of_lt h'],
      simp [succ_pred_eq_of_pos (nat.sub_pos_of_lt h)],
      rw [-succ_pred_eq_of_pos (nat.sub_pos_of_lt h')]},
    assert h' : m * k ≤ m * n,
      exact mul_le_mul_left _ h,
    rw [sub_nat_nat_of_ge h, sub_nat_nat_of_ge h'], simp
  },
  assert h₂ : of_nat 0 = 0, exact rfl,
  subst h₀, simp [h₂, int.zero_mul]
end

private theorem neg_of_nat_add (m n : ℕ) :
  neg_of_nat m + neg_of_nat n = neg_of_nat (m + n) :=
begin
  cases m,
    cases n,
      simp,
      simp,
  cases n,
    simp,
    simp [nat.succ_add]
end

private theorem neg_succ_of_nat_mul_sub_nat_nat (m n k : ℕ) :
  -[1+ m] * sub_nat_nat n k = sub_nat_nat (succ m * k) (succ m * n) :=
begin
  note h := nat.lt_or_ge n k,
  cases h with h h,
  { assert h' : succ m * n < succ m * k,
      exact nat.mul_lt_mul_of_pos_left h (nat.succ_pos m),
    rw [sub_nat_nat_of_lt h, sub_nat_nat_of_ge (le_of_lt h')],
    simp [succ_pred_eq_of_pos (nat.sub_pos_of_lt h)]},
  assert h' : n > k ∨ k = n,
    exact lt_or_eq_of_le h,
  cases h' with h' h',
  { assert h₁ : succ m * n > succ m * k,
      exact nat.mul_lt_mul_of_pos_left h' (nat.succ_pos m),
    rw [sub_nat_nat_of_ge h, sub_nat_nat_of_lt h₁], simp,
    rw [nat.mul_comm k, nat.mul_comm n, -succ_pred_eq_of_pos (nat.sub_pos_of_lt h₁)]
  },
  subst h', simp
end

local attribute [simp] of_nat_mul_sub_nat_nat neg_of_nat_add neg_succ_of_nat_mul_sub_nat_nat

protected theorem distrib_left : ∀ a b c : ℤ, a * (b + c) = a * b + a * c
| (of_nat m) (of_nat n) (of_nat k) := by simp [nat.left_distrib]
| (of_nat m) (of_nat n) -[1+ k]    := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw -sub_nat_nat_add end
| (of_nat m) -[1+ n]    (of_nat k) := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw [int.add_comm, -sub_nat_nat_add] end
| (of_nat m) -[1+ n]   -[1+ k]     := begin simp, rw [-nat.left_distrib, succ_add] end
| -[1+ m]    (of_nat n) (of_nat k) := begin simp, rw [-nat.right_distrib, mul_comm] end
| -[1+ m]    (of_nat n) -[1+ k]    := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw [int.add_comm, -sub_nat_nat_add] end
| -[1+ m]    -[1+ n]    (of_nat k) := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw [-sub_nat_nat_add] end
| -[1+ m]    -[1+ n]   -[1+ k]     := begin simp, rw [-nat.left_distrib, succ_add] end

protected theorem distrib_right (a b c : ℤ) : (a + b) * c = a * c + b * c :=
begin rw [int.mul_comm, int.distrib_left], simp [int.mul_comm] end

instance : comm_ring int :=
{ add            := int.add,
  add_assoc      := int.add_assoc,
  zero           := int.zero,
  zero_add       := int.zero_add,
  add_zero       := int.add_zero,
  neg            := int.neg,
  add_left_inv   := int.add_left_inv,
  add_comm       := int.add_comm,
  mul            := int.mul,
  mul_assoc      := int.mul_assoc,
  one            := 1,
  one_mul        := int.one_mul,
  mul_one        := int.mul_one,
  left_distrib   := int.distrib_left,
  right_distrib  := int.distrib_right,
  mul_comm       := int.mul_comm }

protected theorem zero_ne_one : (0 : int) ≠ 1 :=
assume h : 0 = 1, succ_ne_zero _ (of_nat.inj h)^.symm

/-
protected theorem eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : ℤ}, a * b = 0 → a = 0 ∨ b = 0
| (of_nat n) (of_nat m) h := begin simp end
| (of_nat n) -[1+ m]    h := begin simp end
| -[1+ n]    (of_nat m) h := begin simp end
| -[1+ n]    -[1+m]     h := begin simp end
-/

end int

/-

/- nat abs -/

theorem nat_abs_add_le (a b : ℤ) : nat_abs (a + b) ≤ nat_abs a + nat_abs b := sorry

theorem nat_abs_neg_of_nat (n : nat) : nat_abs (neg_of_nat n) = n :=
begin cases n, reflexivity, reflexivity end

section
local attribute nat_abs [reducible]
theorem nat_abs_mul : Π (a b : ℤ), nat_abs (a * b) = (nat_abs a) * (nat_abs b)
| (of_nat m) (of_nat n) := rfl
| (of_nat m) -[1+ n]    := by rewrite [mul_of_nat_neg_succ_of_nat, nat_abs_neg_of_nat]
| -[1+ m]    (of_nat n) := by rewrite [mul_neg_succ_of_nat_of_nat, nat_abs_neg_of_nat]
| -[1+ m]    -[1+ n]    := rfl
end

/- additional properties -/
theorem of_nat_sub {m n : ℕ} (H : m ≥ n) : of_nat (m - n) = of_nat m - of_nat n :=
have m - n + n = m,     from nat.sub_add_cancel H,
begin
  symmetry,
  apply sub_eq_of_eq_add,
  rewrite [-of_nat_add, this]
end

theorem neg_succ_of_nat_eq' (m : ℕ) : -[1+ m] = -m - 1 :=
by rewrite [neg_succ_of_nat_eq, neg_add]

def succ (a : ℤ) := a + (succ zero)
def pred (a : ℤ) := a - (succ zero)
def nat_succ_eq_int_succ (n : ℕ) : nat.succ n = int.succ n := rfl
theorem pred_succ (a : ℤ) : pred (succ a) = a := !sub_add_cancel
theorem succ_pred (a : ℤ) : succ (pred a) = a := !add_sub_cancel

theorem neg_succ (a : ℤ) : -succ a = pred (-a) :=
by rewrite [↑succ,neg_add]

theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a :=
by rewrite [neg_succ,succ_pred]

theorem neg_pred (a : ℤ) : -pred a = succ (-a) :=
by rewrite [↑pred,neg_sub,sub_eq_add_neg,add.comm]

theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a :=
by rewrite [neg_pred,pred_succ]

theorem pred_nat_succ (n : ℕ) : pred (nat.succ n) = n := pred_succ n
theorem neg_nat_succ (n : ℕ) : -nat.succ n = pred (-n) := !neg_succ
theorem succ_neg_nat_succ (n : ℕ) : succ (-nat.succ n) = -n := !succ_neg_succ

attribute [unfold 2]
def rec_nat_on {P : ℤ → Type} (z : ℤ) (H0 : P 0)
  (Hsucc : Π⦃n : ℕ⦄, P n → P (succ n)) (Hpred : Π⦃n : ℕ⦄, P (-n) → P (-nat.succ n)) : P z :=
int.rec (nat.rec H0 Hsucc) (λn, nat.rec H0 Hpred (nat.succ n)) z

--the only computation rule of rec_nat_on which is not defintional
theorem rec_nat_on_neg {P : ℤ → Type} (n : nat) (H0 : P zero)
  (Hsucc : Π⦃n : nat⦄, P n → P (succ n)) (Hpred : Π⦃n : nat⦄, P (-n) → P (-nat.succ n))
  : rec_nat_on (-nat.succ n) H0 Hsucc Hpred = Hpred (rec_nat_on (-n) H0 Hsucc Hpred) :=
nat.rec rfl (λn H, rfl) n

end int

-/
