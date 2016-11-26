/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers. We show that int is an instance of linear_comm_ordered_ring
and transfer the results.
-/
import .basic

--open nat

-- TODO: are these unification hints the right way to go?

@[unify]
definition nat_zero_hint : unification_hint :=
{ pattern     := nat.zero ≟ (0 : nat),
  constraints := [] }

example : nat.zero = 0 := by simp

@[unify]
definition int_zero_hint (n : ℕ) (s : has_zero ℤ) : unification_hint :=
{ pattern     := @zero int s ≟ int.of_nat n,
  constraints := [n ≟ (0 : nat)] }

example : 0 = int.of_nat 0 := by simp

-- We should probably hide of_nat from the user and rely on ↑n as much as possible, but this
-- unification hint will fix any leaks.

@[unify]
definition coe_nat_int_hint (n m : ℕ) : unification_hint :=
{ pattern     := ↑n ≟ int.of_nat m,
  constraints := [n ≟ m] }

example (n : ℕ) : ↑n = int.of_nat n := by simp

section
universe variable uu
variable α : Type

@[unify]
definition zero_hint (s t : has_zero α) : unification_hint :=
{ pattern     := @zero α s ≟ @zero α t,
  constraints := [] }

@[unify]
definition one_hint (s t : has_one α) : unification_hint :=
{ pattern     := @one α s ≟ @one α t,
  constraints := [] }

@[unify]
definition add_hint (a b c d : α) (s t : has_add α) : unification_hint :=
{ pattern     := @add α s a b ≟ @add α t c d,
  constraints := [a ≟ c, b ≟ d] }

@[unify]
definition mul_hint (a b c d : α) (s t : has_mul α) : unification_hint :=
{ pattern     := @mul α s a b ≟ @mul α t c d,
  constraints := [a ≟ c, b ≟ d] }

@[unify]
definition neg_hint (a b : α) (s t : has_neg α) : unification_hint :=
{ pattern     := @neg α s a ≟ @neg α t b,
  constraints := [a ≟ b] }

end

example (a : ℤ) : a + 0 = a := int.add_zero a

example (a : ℤ) : a + 0 = a := by rw [add_zero a]

example (a : ℤ) : a + 0 = a := by rw [int.add_zero a]


namespace int

@[reducible] private def nonneg (a : ℤ) : Prop := int.cases_on a (take n, true) (take n, false)
protected def le (a b : ℤ) : Prop := nonneg (b - a)

instance : has_le int := has_le.mk int.le

protected def lt (a b : ℤ) : Prop := (a + 1) ≤ b

instance : has_lt int := has_lt.mk int.lt

private def decidable_nonneg (a : ℤ) : decidable (nonneg a) :=
int.cases_on a (take a, decidable.true) (take a, decidable.false)

attribute [instance]
def decidable_le (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _

attribute [instance]
def decidable_lt (a b : ℤ) : decidable (a < b) := decidable_nonneg _

private theorem nonneg.elim {a : ℤ} : nonneg a → ∃ n : ℕ, a = n :=
int.cases_on a (take n H, exists.intro n rfl) (take n', false.elim)

private theorem nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) :=
int.cases_on a (take n, or.inl trivial) (take n, or.inr trivial)

theorem le.intro {a b : ℤ} {n : ℕ} (h : a + n = b) : a ≤ b :=
have ↑n = b - a, begin rw -h, simp end,
show nonneg (b - a), from this ▸ trivial

theorem le.elim {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, a + n = b :=
match (nonneg.elim h) with
| ⟨n, h₁⟩ := exists.intro n begin rw [-h₁, add_comm], simp end
end

protected theorem le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
or.imp_right
  (assume H : nonneg (-(b - a)),
   have -(b - a) = a - b, from neg_sub _ _,
   show nonneg (a - b), from this ▸ H)
  (nonneg_or_nonneg_neg (b - a))

theorem of_nat_le_of_nat_of_le {m n : ℕ} (h : m ≤ n) : of_nat m ≤ of_nat n :=
match nat.le.elim h with
| ⟨k, (hk : m + k = n)⟩ := le.intro (by rw [-hk])
end

theorem le_of_of_nat_le_of_nat {m n : ℕ} (h : of_nat m ≤ of_nat n) : m ≤ n :=
match le.elim h with
| ⟨k, (hk : of_nat m + of_nat k = of_nat n)⟩ :=
    have m + k = n, from of_nat_inj ((of_nat_add m k)^.trans hk),
    nat.le.intro this
end

theorem of_nat_le_of_nat_iff (m n : ℕ) : of_nat m ≤ of_nat n ↔ m ≤ n :=
iff.intro le_of_of_nat_le_of_nat of_nat_le_of_nat_of_le

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + nat.succ n :=
le.intro (show a + 1 + n = a + nat.succ n, by simp [int_coe_eq])

theorem lt.intro {a b : ℤ} {n : ℕ} (h : a + nat.succ n = b) : a < b :=
h ▸ lt_add_succ a n

theorem lt.elim {a b : ℤ} (h : a < b) : ∃ n : ℕ, a + nat.succ n = b :=
match (le.elim h) with
| ⟨n, (hn : a + 1 + n = b)⟩ :=
    exists.intro n begin rw [-hn, add_assoc, add_comm (1 : int)]  end
end

-- TODO: temporary
theorem lt_iff_add_one_le (a b : ℤ) : a < b ↔ a + 1 ≤ b := iff.refl _
theorem nat.lt_iff_add_one_le (a b : ℕ) : a < b ↔ a + 1 ≤ b := iff.refl _

theorem of_nat_lt_of_nat_iff (n m : ℕ) : of_nat n < of_nat m ↔ n < m :=
by rw [lt_iff_add_one_le, -of_nat_succ, of_nat_le_of_nat_iff]

theorem lt_of_of_nat_lt_of_nat {m n : ℕ} (h : of_nat m < of_nat n) : m < n :=
(of_nat_lt_of_nat_iff  _ _)^.mp h

theorem of_nat_lt_of_nat_of_lt {m n : ℕ} (h : m < n) : of_nat m < of_nat n :=
(of_nat_lt_of_nat_iff _ _)^.mpr h

/- show that the integers form an ordered additive group -/

protected theorem le_refl (a : ℤ) : a ≤ a :=
le.intro (add_zero a)

protected theorem le_trans {a b c : ℤ} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
match le.elim h1, le.elim h2 with
| ⟨n, (hn : a + n = b)⟩, ⟨m, (hm : b + m = c)⟩ :=
  begin apply le.intro, rw [-hm, -hn, add_assoc] end
end

protected theorem le_antisymm {a b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
match le.elim h₁, le.elim h₂ with
| ⟨n, (hn : a + of_nat n = b)⟩, ⟨m, (hm : b + of_nat m = a)⟩ :=
    have a + of_nat (n + m) = a + 0, by rw [of_nat_add, -add_assoc, hn, hm, add_zero a],
    have of_nat (n + m) = 0, from add_left_cancel this,
    have n + m = 0, from of_nat_inj this,
    have n = 0, from nat.eq_zero_of_add_eq_zero_right this,
    show a = b, begin rw [-hn, this, add_zero a] end

end

protected theorem lt_irrefl (a : ℤ) : ¬ a < a :=
(suppose a < a,
  match lt.elim this with
  | ⟨n, (hn : a + nat.succ n = a)⟩ :=
      have a + nat.succ n = a + 0, by simp [hn],
      have nat.succ n = 0, from of_nat_inj (add_left_cancel this),
      show false, from nat.succ_ne_zero _ this
  end)

protected theorem ne_of_lt {a b : ℤ} (h : a < b) : a ≠ b :=
(suppose a = b, absurd (begin rewrite this at h, exact h end) (int.lt_irrefl b))

theorem le_of_lt {a b : ℤ} (h : a < b) : a ≤ b :=
match lt.elim h with
| ⟨n, (hn : a + nat.succ n = b)⟩ := le.intro hn
end

-- TODO: put in nat library, or make sure this is automatic
private lemma nat_pos_of_ne_zero {n : nat} (h : n ≠ 0) : n > 0 :=
begin cases n, contradiction, apply nat.zero_lt_succ end

protected theorem lt_iff_le_and_ne (a b : ℤ) : a < b ↔ (a ≤ b ∧ a ≠ b) :=
iff.intro
  (assume h, and.intro (le_of_lt h) (int.ne_of_lt h))
  (assume ⟨aleb, aneb⟩,
    match le.elim aleb with
    | ⟨n, (hn : a + n = b)⟩ :=
        have n ≠ 0,
          from (suppose n = 0, aneb (begin rw [-hn, this, int_coe_eq, int.add_zero] end)),
        have n = nat.succ (nat.pred n),
          from eq.symm (nat.succ_pred_eq_of_pos (nat_pos_of_ne_zero this)),
        lt.intro (begin rewrite this at hn, exact hn end)
    end)

protected theorem le_iff_lt_or_eq (a b : ℤ) : a ≤ b ↔ (a < b ∨ a = b) :=
iff.intro
  (assume h,
    decidable.by_cases
      (suppose a = b, or.inr this)
      (suppose a ≠ b,
        match le.elim h with
        | ⟨n, (hn : a + n = b)⟩ :=
            have n ≠ 0, from
              (suppose n = 0, ‹a ≠ b› begin rw [-hn, this, int_coe_eq, int.add_zero] end),
            have n = nat.succ (nat.pred n),
              from eq.symm (nat.succ_pred_eq_of_pos (nat_pos_of_ne_zero this)),
            or.inl (lt.intro (begin rewrite this at hn, exact hn end))
        end))
  (assume h,
    or.elim h
      (assume h', le_of_lt h')
      (assume h', h' ▸ int.le_refl a))

theorem lt_succ (a : ℤ) : a < a + 1 :=
int.le_refl (a + 1)

protected theorem add_le_add_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
match le.elim h with
| ⟨n, (hn : a + n = b)⟩ := le.intro (show c + a + n = c + b, begin rw [add_assoc, hn] end)
end

protected theorem add_lt_add_left {a b : ℤ} (h : a < b) (c : ℤ) : c + a < c + b :=
iff.mpr (int.lt_iff_le_and_ne _ _)
  (and.intro
    (int.add_le_add_left (le_of_lt h) _)
    (take heq, int.lt_irrefl b begin rw add_left_cancel heq at h, exact h end))

protected theorem mul_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
match le.elim ha, le.elim hb with
| ⟨n, hn⟩, ⟨m, hm⟩ :=
    le.intro (show 0 + ↑n * ↑m = a * b, begin rw [-hn, -hm], simp end)
end

protected theorem mul_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
match lt.elim ha, lt.elim hb with
| ⟨n, hn⟩, ⟨m, hm⟩ :=
    lt.intro (show 0 + ↑(nat.succ (nat.succ n * m + n)) = a * b,
      begin rw [-hn, -hm], simp, rw [-of_nat_mul], simp [nat.mul_succ, nat.succ_add] end)
end

protected theorem zero_lt_one : (0 : ℤ) < 1 := trivial

end int

/-
protected theorem not_le_of_gt {a b : ℤ} (H : a < b) : ¬ b ≤ a :=
  assume Hba,
  let Heq := int.le_antisymm (le_of_lt H) Hba in
  !int.lt_irrefl (Heq ▸ H)

protected theorem lt_of_lt_of_le {a b c : ℤ} (Hab : a < b) (Hbc : b ≤ c) : a < c :=
  let Hab' := le_of_lt Hab in
  let Hac := int.le_trans Hab' Hbc in
  (iff.mpr !int.lt_iff_le_and_ne) (and.intro Hac
    (assume Heq, int.not_le_of_gt (Heq ▸ Hab) Hbc))

protected theorem lt_of_le_of_lt  {a b c : ℤ} (Hab : a ≤ b) (Hbc : b < c) : a < c :=
  let Hbc' := le_of_lt Hbc in
  let Hac := int.le_trans Hab Hbc' in
  (iff.mpr !int.lt_iff_le_and_ne) (and.intro Hac
    (assume Heq, int.not_le_of_gt (Heq⁻¹ ▸ Hbc) Hab))

attribute [trans_instance]
protected def linear_ordered_comm_ring :
    linear_ordered_comm_ring int :=
⦃linear_ordered_comm_ring, int.integral_domain,
  le               := int.le,
  le_refl          := int.le_refl,
  le_trans         := @int.le_trans,
  le_antisymm      := @int.le_antisymm,
  lt               := int.lt,
  le_of_lt         := @int.le_of_lt,
  lt_irrefl        := int.lt_irrefl,
  lt_of_lt_of_le   := @int.lt_of_lt_of_le,
  lt_of_le_of_lt   := @int.lt_of_le_of_lt,
  add_le_add_left  := @int.add_le_add_left,
  mul_nonneg       := @int.mul_nonneg,
  mul_pos          := @int.mul_pos,
  le_iff_lt_or_eq  := int.le_iff_lt_or_eq,
  le_total         := int.le_total,
  zero_ne_one      := int.zero_ne_one,
  zero_lt_one      := int.zero_lt_one,
  add_lt_add_left  := @int.add_lt_add_left⦄

attribute [instance]
protected def decidable_linear_ordered_comm_ring :
    decidable_linear_ordered_comm_ring int :=
⦃decidable_linear_ordered_comm_ring,
 int.linear_ordered_comm_ring,
 decidable_lt := decidable_lt⦄

/- more facts specific to int -/

theorem of_nat_nonneg (n : ℕ) : 0 ≤ of_nat n := trivial

theorem of_nat_pos {n : ℕ} (Hpos : #nat n > 0) : of_nat n > 0 :=
of_nat_lt_of_nat_of_lt Hpos

theorem of_nat_succ_pos (n : nat) : of_nat (nat.succ n) > 0 :=
of_nat_pos !nat.succ_pos

theorem exists_eq_of_nat {a : ℤ} (H : 0 ≤ a) : ∃n : ℕ, a = of_nat n :=
obtain (n : ℕ) (H1 : 0 + of_nat n = a), from le.elim H,
exists.intro n (!zero_add ▸ (H1⁻¹))

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -(of_nat n) :=
have -a ≥ 0, from iff.mpr !neg_nonneg_iff_nonpos H,
obtain (n : ℕ) (Hn : -a = of_nat n), from exists_eq_of_nat this,
exists.intro n (eq_neg_of_eq_neg (Hn⁻¹))

theorem of_nat_nat_abs_of_nonneg {a : ℤ} (H : a ≥ 0) : of_nat (nat_abs a) = a :=
obtain (n : ℕ) (Hn : a = of_nat n), from exists_eq_of_nat H,
Hn⁻¹ ▸ congr_arg of_nat (nat_abs_of_nat n)

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : of_nat (nat_abs a) = -a :=
have -a ≥ 0, from iff.mpr !neg_nonneg_iff_nonpos H,
calc
  of_nat (nat_abs a) = of_nat (nat_abs (-a)) : nat_abs_neg
                 ... = -a                    : of_nat_nat_abs_of_nonneg this

theorem of_nat_nat_abs (b : ℤ) : nat_abs b = abs b :=
or.elim (le.total 0 b)
  (assume H : b ≥ 0, of_nat_nat_abs_of_nonneg H ⬝ (abs_of_nonneg H)⁻¹)
  (assume H : b ≤ 0, of_nat_nat_abs_of_nonpos H ⬝ (abs_of_nonpos H)⁻¹)

theorem nat_abs_abs (a : ℤ) : nat_abs (abs a) = nat_abs a :=
abs.by_cases rfl !nat_abs_neg

theorem lt_of_add_one_le {a b : ℤ} (H : a + 1 ≤ b) : a < b :=
obtain (n : nat) (H1 : a + 1 + n = b), from le.elim H,
have a + succ n = b, by rewrite [-H1, add.assoc, add.comm 1],
lt.intro this

theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b :=
obtain (n : nat) (H1 : a + succ n = b), from lt.elim H,
have a + 1 + n = b, by rewrite [-H1, add.assoc, add.comm 1],
le.intro this

theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
lt_add_of_le_of_pos H trivial

theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
have H1 : a + 1 ≤ b + 1, from add_one_le_of_lt H,
le_of_add_le_add_right H1

theorem sub_one_le_of_lt {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
lt_of_add_one_le (begin rewrite sub_add_cancel, exact H end)

theorem lt_of_sub_one_le {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
!sub_add_cancel ▸ add_one_le_of_lt H

theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
le_of_lt_add_one begin rewrite sub_add_cancel, exact H end

theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
!sub_add_cancel ▸ (lt_add_one_of_le H)

theorem sign_of_succ (n : nat) : sign (nat.succ n) = 1 :=
sign_of_pos (of_nat_pos !nat.succ_pos)

theorem exists_eq_neg_succ_of_nat {a : ℤ} : a < 0 → ∃m : ℕ, a = -[1+m] :=
int.cases_on a
  (take (m : nat) H, absurd (of_nat_nonneg m : 0 ≤ m) (not_le_of_gt H))
  (take (m : nat) H, exists.intro m rfl)

theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : a ≥ 0) (H' : a * b = 1) : a = 1 :=
have a * b > 0, by rewrite H'; apply trivial,
have b > 0, from pos_of_mul_pos_left this H,
have a > 0, from pos_of_mul_pos_right `a * b > 0` (le_of_lt `b > 0`),
or.elim (le_or_gt a 1)
  (suppose a ≤ 1,
    show a = 1, from le.antisymm this (add_one_le_of_lt `a > 0`))
  (suppose a > 1,
    have a * b ≥ 2 * 1,
      from mul_le_mul (add_one_le_of_lt `a > 1`) (add_one_le_of_lt `b > 0`) trivial H,
    have false, by rewrite [H' at this]; exact this,
    false.elim this)

theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : b ≥ 0) (H' : a * b = 1) : b = 1 :=
eq_one_of_mul_eq_one_right H (!mul.comm ▸ H')

theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
eq_of_mul_eq_mul_right Hpos (H ⬝ (one_mul a)⁻¹)

theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
eq_one_of_mul_eq_self_left Hpos (!mul.comm ▸ H)

theorem eq_one_of_dvd_one {a : ℤ} (H : a ≥ 0) (H' : a ∣ 1) : a = 1 :=
dvd.elim H'
  (take b,
    suppose 1 = a * b,
    eq_one_of_mul_eq_one_right H this⁻¹)

theorem exists_least_of_bdd {P : ℤ → Prop} [HP : decidable_pred P]
    (Hbdd : ∃ b : ℤ, ∀ z : ℤ, z ≤ b → ¬ P z)
        (Hinh : ∃ z : ℤ, P z) : ∃ lb : ℤ, P lb ∧ (∀ z : ℤ, z < lb → ¬ P z) :=
  begin
    cases Hbdd with [b, Hb],
    cases Hinh with [elt, Helt],
    existsi b + of_nat (least (λ n, P (b + of_nat n)) (nat.succ (nat_abs (elt - b)))),
    have Heltb : elt > b, begin
      apply lt_of_not_ge,
      intro Hge,
      apply (Hb _ Hge) Helt
    end,
    have H' : P (b + of_nat (nat_abs (elt - b))), begin
      rewrite [of_nat_nat_abs_of_nonneg (int.le_of_lt (iff.mpr !sub_pos_iff_lt Heltb)),
              add.comm, sub_add_cancel],
      apply Helt
    end,
    apply and.intro,
    apply least_of_lt _ !lt_succ_self H',
    intros z Hz,
    cases em (z ≤ b) with [Hzb, Hzb],
    apply Hb _ Hzb,
    let Hzb' := lt_of_not_ge Hzb,
    let Hpos := iff.mpr !sub_pos_iff_lt Hzb',
    have Hzbk : z = b + of_nat (nat_abs (z - b)),
      by rewrite [of_nat_nat_abs_of_nonneg (int.le_of_lt Hpos), int.add_comm, sub_add_cancel],
    have Hk : nat_abs (z - b) < least (λ n, P (b + of_nat n)) (nat.succ (nat_abs (elt - b))), begin
     note Hz' := iff.mp !lt_add_iff_sub_lt_left Hz,
     rewrite [-of_nat_nat_abs_of_nonneg (int.le_of_lt Hpos) at Hz'],
     apply lt_of_of_nat_lt_of_nat Hz'
    end,
    let Hk' := not_le_of_gt Hk,
    rewrite Hzbk,
    apply λ p, mt (ge_least_of_lt _ p) Hk',
    apply nat.lt_trans Hk,
    apply least_lt _ !lt_succ_self H'
  end

theorem exists_greatest_of_bdd {P : ℤ → Prop} [HP : decidable_pred P]
    (Hbdd : ∃ b : ℤ, ∀ z : ℤ, z ≥ b → ¬ P z)
        (Hinh : ∃ z : ℤ, P z) : ∃ ub : ℤ, P ub ∧ (∀ z : ℤ, z > ub → ¬ P z) :=
  begin
    cases Hbdd with [b, Hb],
    cases Hinh with [elt, Helt],
    existsi b - of_nat (least (λ n, P (b - of_nat n)) (nat.succ (nat_abs (b - elt)))),
    have Heltb : elt < b, begin
      apply lt_of_not_ge,
      intro Hge,
      apply (Hb _ Hge) Helt
    end,
    have H' : P (b - of_nat (nat_abs (b - elt))), begin
      rewrite [of_nat_nat_abs_of_nonneg (int.le_of_lt (iff.mpr !sub_pos_iff_lt Heltb)),
              sub_sub_self],
      apply Helt
    end,
    apply and.intro,
    apply least_of_lt _ !lt_succ_self H',
    intros z Hz,
    cases em (z ≥ b) with [Hzb, Hzb],
    apply Hb _ Hzb,
    let Hzb' := lt_of_not_ge Hzb,
    let Hpos := iff.mpr !sub_pos_iff_lt Hzb',
    have Hzbk : z = b - of_nat (nat_abs (b - z)),
      by rewrite [of_nat_nat_abs_of_nonneg (int.le_of_lt Hpos), sub_sub_self],
    have Hk : nat_abs (b - z) < least (λ n, P (b - of_nat n)) (nat.succ (nat_abs (b - elt))), begin
      note Hz' := iff.mp !lt_add_iff_sub_lt_left (iff.mpr !lt_add_iff_sub_lt_right Hz),
      rewrite [-of_nat_nat_abs_of_nonneg (int.le_of_lt Hpos) at Hz'],
      apply lt_of_of_nat_lt_of_nat Hz'
    end,
    let Hk' := not_le_of_gt Hk,
    rewrite Hzbk,
    apply λ p, mt (ge_least_of_lt _ p) Hk',
    apply nat.lt_trans Hk,
    apply least_lt _ !lt_succ_self H'
  end

end int
-/
