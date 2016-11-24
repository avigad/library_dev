/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
import ..nat.sub
open nat

/- the type, coercions, and notation -/

inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int

notation `ℤ` := int

instance coe_nat_to_int : has_coe nat int :=
⟨int.of_nat⟩

lemma int_coe_eq (n : ℕ) : ↑n = int.of_nat n := rfl

notation `-[1+ ` n `]` := int.neg_succ_of_nat n

-- TODO: should this work? Instead, we do it lower down.
-- instance decidable_eq int := by tactic.mk_dec_eq_instance


namespace int

-- TODO: should these be only local, until the ring instance is declared?
instance : has_zero ℤ := ⟨of_nat 0⟩
instance : has_one ℤ := ⟨of_nat 1⟩

theorem of_nat_zero : of_nat (0 : nat) = (0 : int) :=
rfl

theorem of_nat_one : of_nat (1 : nat) = (1 : int) :=
rfl

/- definitions of basic functions -/

def neg_of_nat : ℕ → ℤ
| 0        := 0
| (succ m) := -[1+ m]

def sub_nat_nat (m n : ℕ) : ℤ :=
match (n - m : nat) with
| 0        := of_nat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k
end

-- TODO: this should be handled by the equation generator
lemma sub_nat_nat_of_sub_eq_zero {m n : ℕ} (h : n - m = 0) : sub_nat_nat m n = of_nat (m - n) :=
begin unfold sub_nat_nat, rw [h, sub_nat_nat._match_1.equations.eqn_1] end

lemma sub_nat_nat_of_sub_eq_succ {m n k : ℕ} (h : n - m = succ k) : sub_nat_nat m n = -[1+ k] :=
begin unfold sub_nat_nat, rw [h, sub_nat_nat._match_1.equations.eqn_2] end

protected definition neg : ℤ → ℤ
| (of_nat n) := neg_of_nat n
| -[1+ n]    := succ n

protected definition add : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m + n)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m]    (of_nat n) := sub_nat_nat n (succ m)
| -[1+ m]    -[1+ n]    := -[1+ succ (m + n)]

protected definition mul : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m * n)
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m]    (of_nat n) := neg_of_nat (succ m * n)
| -[1+ m]    -[1+ n]    := of_nat (succ m * succ n)

instance : has_neg ℤ := ⟨int.neg⟩
instance : has_add ℤ := ⟨int.add⟩
instance : has_mul ℤ := ⟨int.mul⟩

-- TODO: maybe this should all be made local attributes?

@[simp] lemma of_nat_add_of_nat (m n : nat) : of_nat m + of_nat n = of_nat (m + n) := rfl
@[simp] lemma of_nat_add_neg_succ_of_nat (m n : nat) :
                of_nat m + -[1+ n] = sub_nat_nat m (succ n) := rfl
@[simp] lemma neg_succ_of_nat_add_of_nat (m n : nat) :
                -[1+ m] + of_nat n = sub_nat_nat n (succ m) := rfl
@[simp] lemma neg_succ_of_nat_add_neg_succ_of_nat (m n : nat) :
                -[1+ m] + -[1+ n] = -[1+ succ (m + n)] := rfl

@[simp] lemma of_nat_mul_of_nat   (m n : nat) : of_nat m * of_nat n = of_nat (m * n) := rfl
@[simp] lemma of_nat_mul_neg_succ_of_nat (m n : nat) :
                of_nat m * -[1+ n] = neg_of_nat (m * succ n) := rfl
@[simp] lemma neg_succ_of_nat_of_nat (m n : nat) :
                -[1+ m] * of_nat n = neg_of_nat (succ m * n) := rfl
@[simp] lemma mul_neg_succ_of_nat_neg_succ_of_nat (m n : nat) :
               -[1+ m] * -[1+ n] = of_nat (succ m * succ n) := rfl

@[simp] lemma neg_of_nat_zero : -(of_nat 0) = 0 := rfl
@[simp] lemma neg_of_nat_of_succ (n : ℕ) : -(of_nat (succ n)) = -[1+ n] := rfl
@[simp] lemma neg_neg_of_nat_succ (n : ℕ) : -(-[1+ n]) = of_nat (succ n) := rfl

--@[simp] lemma neg_of_nat_of_succ (n : nat) : neg_of_nat (succ n) = -[1+ n] := rfl


/- some basic functions and properties -/

-- TODO: decide which notation to use
theorem of_nat_inj {m n : ℕ} (h : of_nat m = of_nat n) : m = n :=
int.no_confusion h id

theorem eq_of_of_nat_eq_of_nat {m n : ℕ} (h : of_nat m = of_nat n) : m = n :=
of_nat_inj h

theorem of_nat_eq_of_nat_iff (m n : ℕ) : of_nat m = of_nat n ↔ m = n :=
iff.intro of_nat_inj (congr_arg _)

theorem neg_succ_of_nat_inj {m n : ℕ} (h : neg_succ_of_nat m = neg_succ_of_nat n) : m = n :=
int.no_confusion h id

theorem neg_succ_of_nat_eq (n : ℕ) : -[1+ n] = -(n + 1) := rfl

-- TODO: can this be done automatically
instance : decidable_eq int
| (int.of_nat m) (int.of_nat n) := if h : m = n then decidable.is_true (congr_arg _ h)
                                   else decidable.is_false (λ h', h (of_nat_inj h'))
| (int.of_nat m) -[1+ n]        := decidable.is_false (begin intro h, contradiction end)
| -[1+ m]        (int.of_nat n) := decidable.is_false (begin intro h, contradiction end)
| -[1+ m]        -[1+ n]        := if h : m = n then decidable.is_true (congr_arg _ h)
                                   else decidable.is_false (λ h', h (neg_succ_of_nat_inj h'))

theorem of_nat_add (n m : nat) : of_nat (n + m) = of_nat n + of_nat m := rfl

theorem of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 := rfl

theorem of_nat_mul (n m : ℕ) : of_nat (n * m) = of_nat n * of_nat m := rfl

theorem sub_nat_nat_of_ge {m n : ℕ} (h : m ≥ n) : sub_nat_nat m n = of_nat (m - n) :=
sub_nat_nat_of_sub_eq_zero (sub_eq_zero_of_le h)

theorem sub_nat_nat_of_lt {m n : ℕ} (h : m < n) : sub_nat_nat m n = -[1+ pred (n - m)] :=
have n - m = succ (pred (n - m)), from eq.symm (succ_pred_eq_of_pos (nat.sub_pos_of_lt h)),
by rewrite sub_nat_nat_of_sub_eq_succ this

theorem sub_nat_of_lt' {m n : ℕ} (h : m < n) : sub_nat_nat m n = neg_of_nat (n - m) :=
by rewrite [sub_nat_nat_of_lt h, -neg_of_nat_of_succ, succ_pred_eq_of_pos (nat.sub_pos_of_lt h)]

definition nat_abs (a : ℤ) : ℕ := int.cases_on a id succ

theorem nat_abs_of_nat (n : ℕ) : nat_abs n = n := rfl

theorem eq_zero_of_nat_abs_eq_zero : Π {a : ℤ}, nat_abs a = 0 → a = 0
| (of_nat m) H := congr_arg of_nat H
| -[1+ m']   H := absurd H (succ_ne_zero _)

theorem nat_abs_zero : nat_abs (0 : int) = (0 : nat) :=
rfl

theorem nat_abs_one : nat_abs (1 : int) = (1 : nat) :=
rfl

/-
   int is a ring
-/

/- addition -/

protected theorem add_zero : ∀ a : ℤ, a + 0 = a
| (of_nat n) := rfl
| -[1+ n]   := rfl

protected theorem zero_add : ∀ a : ℤ, a + 0 = a
| (of_nat n) := rfl
| -[1+ n]   := rfl

protected theorem add_comm : ∀ a b : ℤ, a + b = b + a
| (of_nat n) (of_nat m) := by simp
| (of_nat n) -[1+ m]    := rfl
| -[1+ n]    (of_nat m) := rfl
| -[1+ n]    -[1+m]     := by simp

private lemma sub_nat_nat_add_add (m n k : ℕ) : sub_nat_nat (m + k) (n + k) = sub_nat_nat m n :=
or.elim (le_or_gt n m)
  (assume h : n ≤ m,
    have n + k ≤ m + k, from nat.add_le_add_right h k,
    by simp [sub_nat_nat_of_ge h, sub_nat_nat_of_ge this])
  (assume h : n > m,
    have n + k > m + k, from nat.add_lt_add_right h k,
    by simp [sub_nat_nat_of_lt h, sub_nat_nat_of_lt this])

private lemma sub_nat_nat_sub {m n : ℕ} (h : m ≥ n) (k : ℕ) :
  sub_nat_nat (m - n) k = sub_nat_nat m (k + n) :=
calc
  sub_nat_nat (m - n) k = sub_nat_nat (m - n + n) (k + n) : by rewrite sub_nat_nat_add_add
                    ... = sub_nat_nat m (k + n)           : by rewrite [nat.sub_add_cancel h]

private lemma sub_nat_nat_add (m n k : ℕ) : sub_nat_nat (m + n) k = of_nat m + sub_nat_nat n k :=
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

private lemma sub_nat_nat_add_neg_succ_of_nat (m n k : ℕ) :
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

private lemma add_assoc_aux1 (m n : ℕ) :
    ∀ c : ℤ, of_nat m + of_nat n + c = of_nat m + (of_nat n + c)
| (of_nat k) := by simp
| -[1+ k]    := by simp [sub_nat_nat_add]

private lemma add_assoc_aux2 (m n k : ℕ) :
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

@[simp] lemma sub_nat_self : ∀ n, sub_nat_nat n n = 0
| 0        := rfl
| (succ m) := begin rw [sub_nat_nat_of_sub_eq_zero, nat.sub_self], rw nat.sub_self end

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

@[simp] private lemma of_nat_mul_neg_of_nat (m : ℕ) :
   ∀ n, of_nat m * neg_of_nat n = neg_of_nat (m * n)
| 0        := by simp
| (succ n) := by simp [neg_of_nat.equations.eqn_2]

@[simp] private lemma of_nat_mul_neg_of_nat (m n : ℕ) :
    neg_of_nat m * of_nat n = neg_of_nat (m * n) :=
begin rw int.mul_comm, simp end

@[simp] private lemma neg_succ_of_nat_mul_neg_of_nat (m : ℕ) :
  ∀ n, -[1+ m] * neg_of_nat n = of_nat (succ m * n)
| 0        := by simp
| (succ n) := by simp [neg_of_nat.equations.eqn_2
]
@[simp] private lemma neg_succ_of_nat_mul_neg_of_nat (m n : ℕ) :
  neg_of_nat n * -[1+ m] = of_nat (n * succ m) :=
begin rw int.mul_comm, simp end

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
| (of_nat m) := begin unfold one, simp end
| -[1+ m]    := begin unfold one, simp end

protected theorem one_mul (a : ℤ) : 1 * a = a :=
int.mul_comm a 1 ▸ int.mul_one a


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

/- multiplication -/

protected theorem right_distrib (a b c : ℤ) : (a + b) * c = a * c + b * c :=
sorry

protected theorem left_distrib (a b c : ℤ) : a * (b + c) = a * b + a * c :=
calc
  a * (b + c) = (b + c) * a : int.mul_comm
    ... = b * a + c * a : int.right_distrib
    ... = a * b + c * a : int.mul_comm
    ... = a * b + a * c : int.mul_comm

protected theorem zero_ne_one : (0 : int) ≠ 1 :=
assume H : 0 = 1, !succ_ne_zero (of_nat.inj H)⁻¹

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ∨ b = 0 :=
or.imp eq_zero_of_nat_abs_eq_zero eq_zero_of_nat_abs_eq_zero
  (eq_zero_or_eq_zero_of_mul_eq_zero (by rewrite [-nat_abs_mul, H]))

attribute [trans_instance]
protected definition integral_domain : integral_domain int :=
⦃integral_domain,
  add            := int.add,
  add_assoc      := int.add_assoc,
  zero           := 0,
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
  left_distrib   := int.left_distrib,
  right_distrib  := int.right_distrib,
  mul_comm       := int.mul_comm,
  zero_ne_one    := int.zero_ne_one,
  eq_zero_or_eq_zero_of_mul_eq_zero := @int.eq_zero_or_eq_zero_of_mul_eq_zero⦄

attribute [instance, priority int.prio]
definition int_has_sub : has_sub int :=
has_sub.mk has_sub.sub

attribute [instance, priority int.prio]
definition int_has_dvd : has_dvd int :=
has_dvd.mk has_dvd.dvd

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

definition succ (a : ℤ) := a + (succ zero)
definition pred (a : ℤ) := a - (succ zero)
definition nat_succ_eq_int_succ (n : ℕ) : nat.succ n = int.succ n := rfl
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
definition rec_nat_on {P : ℤ → Type} (z : ℤ) (H0 : P 0)
  (Hsucc : Π⦃n : ℕ⦄, P n → P (succ n)) (Hpred : Π⦃n : ℕ⦄, P (-n) → P (-nat.succ n)) : P z :=
int.rec (nat.rec H0 Hsucc) (λn, nat.rec H0 Hpred (nat.succ n)) z

--the only computation rule of rec_nat_on which is not definitional
theorem rec_nat_on_neg {P : ℤ → Type} (n : nat) (H0 : P zero)
  (Hsucc : Π⦃n : nat⦄, P n → P (succ n)) (Hpred : Π⦃n : nat⦄, P (-n) → P (-nat.succ n))
  : rec_nat_on (-nat.succ n) H0 Hsucc Hpred = Hpred (rec_nat_on (-n) H0 Hsucc Hpred) :=
nat.rec rfl (λn H, rfl) n

end int

-/
