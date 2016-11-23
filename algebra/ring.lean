/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import .group ..logic.todo
open eq

universe variable uu
variable {A : Type uu}

section semiring
  variables [semiring A] (a b c : A)

  theorem one_add_one_eq_two : 1 + 1 = (2 : A) := rfl

  theorem ne_zero_of_mul_ne_zero_right {a b : A} (h : a * b ≠ 0) : a ≠ 0 :=
  suppose a = 0,
  have a * b = 0, by rewrite [this, zero_mul],
  h this

  theorem ne_zero_of_mul_ne_zero_left {a b : A} (h : a * b ≠ 0) : b ≠ 0 :=
  suppose b = 0,
  have a * b = 0, by rewrite [this, mul_zero],
  h this

  local attribute [simp] right_distrib

  theorem distrib_three_right (a b c d : A) : (a + b + c) * d = a * d + b * d + c * d :=
  by simp
end semiring

/- comm semiring -/

section comm_semiring
  variables [comm_semiring A] (a b c : A)

  @[instance] def comm_semiring_has_dvd : has_dvd A :=
  has_dvd.mk (λ a b, ∃ c, b = a * c)

  -- TODO: this used to not have c explicit, but that seems to be important
  --       for use with tactics, similar to exists_intro
  theorem dvd_intro {a b : A} (c : A) (h : a * c = b) : a ∣ b :=
  exists_intro c h^.symm

  def dvd_of_mul_right_eq := @dvd_intro

  theorem dvd_intro_left {a b : A} (c : A) (h : c * a = b) : a ∣ b :=
  dvd_intro _ (begin rewrite mul_comm at h, apply h end)

  def dvd_of_mul_left_eq := @dvd_intro_left

  theorem exists_eq_mul_right_of_dvd {a b : A} (h : a ∣ b) : ∃ c, b = a * c := h

  theorem dvd_elim {P : Prop} {a b : A} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
  exists_elim H₁ H₂

  def dvd.elim := @dvd_elim

  theorem exists_eq_mul_left_of_dvd {a b : A} (h : a ∣ b) : ∃ c, b = c * a :=
  dvd_elim h (take c, assume H1 : b = a * c, exists.intro c (eq.trans H1 (mul_comm a c)))

  theorem dvd.elim_left {P : Prop} {a b : A} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
  exists.elim (exists_eq_mul_left_of_dvd h₁) (take c, assume h₃ : b = c * a, h₂ c h₃)

  @[simp] theorem dvd_refl : a ∣ a :=
  dvd_intro 1 (by simp)

  theorem dvd_trans {a b c : A} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  match h₁, h₂ with
  | ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ :=
    ⟨d * e, show c = a * (d * e), by tactic.simp_using_hs⟩
  end

  def dvd.trans := @dvd_trans

  theorem eq_zero_of_zero_dvd {a : A} (h : 0 ∣ a) : a = 0 :=
  dvd_elim h (take c, assume H' : a = 0 * c, eq.trans H' (zero_mul c))

  @[simp] theorem dvd_zero : a ∣ 0 := dvd_intro 0 (by simp)

  @[simp] theorem one_dvd : 1 ∣ a := dvd_intro a (by simp)

  @[simp] theorem dvd_mul_right : a ∣ a * b := dvd_intro b rfl

  @[simp] theorem dvd_mul_left : a ∣ b * a := dvd_intro b (by simp)

  theorem dvd_mul_of_dvd_left {a b : A} (h : a ∣ b) (c : A) : a ∣ b * c :=
  dvd_elim h (λ c h', by tactic.simp_using_hs)

  theorem dvd_mul_of_dvd_right {a b : A} (h : a ∣ b) (c : A) : a ∣ c * b :=
  begin rewrite mul_comm, exact dvd_mul_of_dvd_left h _ end

  theorem mul_dvd_mul {a b c d : A} (dvd_ab : a ∣ b) (dvd_cd : c ∣ d) : a * c ∣ b * d :=
  dvd_elim dvd_ab (take e, assume beq,
    dvd_elim dvd_cd (take f, assume deq,
      dvd_intro (e *f) (by tactic.simp_using_hs)))

/-
  -- TODO: this should work, but doesn't.
  -- The function definition system says we don't have well-founded recursion

  theorem mul_dvd_mul' {a b c d : A} (dvd_ab : a ∣ b) (dvd_cd : c ∣ d) : a * c ∣ b * d :=
  match dvd_ab, dvd_cd with
  | ⟨e, (he : b = a * e)⟩, ⟨f, (hf : d = c * f)⟩ :=
    begin subst he, subst hf, apply (@dvd_intro A _ _ _ (e * f)), simp end
  end
-/

  theorem dvd_of_mul_right_dvd {a b c : A} (h : a * b ∣ c) : a ∣ c :=
  dvd_elim h (begin intros, tactic.simp_using_hs end)

  theorem dvd_of_mul_left_dvd {a b c : A} (h : a * b ∣ c) : b ∣ c :=
  dvd_elim h (λ d ceq, dvd_intro (a * d) (by tactic.simp_using_hs))
end comm_semiring

/- ring -/

theorem ring.mul_zero [s : ring A] (a : A) : a * 0 = 0 :=
have a * 0 + 0 = a * 0 + a * 0, from calc
  a * 0 + 0 = a * (0 + 0)   : by simp
        ... = a * 0 + a * 0 : by rewrite left_distrib,
show a * 0 = 0, from (add_left_cancel this)^.symm

theorem ring.zero_mul [s : ring A] (a : A) : 0 * a = 0 :=
have 0 * a + 0 = 0 * a + 0 * a, from calc
  0 * a + 0 = (0 + 0) * a   : by simp
        ... = 0 * a + 0 * a : by rewrite right_distrib,
show 0 * a = 0, from  (add_left_cancel this)^.symm

@[instance] def ring.to_semiring [s : ring A] : semiring A :=
{ s with
  mul_zero := ring.mul_zero,
  zero_mul := ring.zero_mul }

section
  variables [ring A] (a b c d e : A)

  @[simp] theorem neg_mul_eq_neg_mul : - a * b = - (a * b) :=
  eq_neg_of_add_eq_zero begin rewrite -right_distrib, simp end

  @[simp] theorem mul_neg_eq_neg_mul_symm : a * - b = - (a * b) :=
  eq_neg_of_add_eq_zero begin rewrite -left_distrib, simp end

  -- TODO: delete these?
  theorem neg_mul_neg : -a * -b = a * b :=
  by simp

  theorem neg_mul_comm : -a * b = a * -b :=
  by simp

  theorem neg_eq_neg_one_mul : -a = -1 * a :=
  by simp

  @[simp] theorem mul_sub_left_distrib : a * (b - c) = a * b - a * c :=
  by simp [sub_eq_add_neg, left_distrib]

  @[simp] theorem mul_sub_right_distrib : (a - b) * c = a * c - b * c :=
  by simp [@sub_eq_add_neg A, @right_distrib A]

  theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp
      ... ↔ a * e + c - b * e = d : iff.symm (sub_eq_iff_eq_add _ _ _)
      ... ↔ (a - b) * e + c = d   : begin simp [@sub_eq_add_neg A, @right_distrib A] end

  theorem mul_add_eq_mul_add_of_sub_mul_add_eq : (a - b) * e + c = d → a * e + c = b * e + d :=
  sorry
--  begin intro h, simp [h^.symm], rewrite (add_comm (b * e)), rewrite sub_add_cancel end

  theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
  assume h,
  calc
    (a - b) * e + c = (a * e + c) - b * e : begin simp [@sub_eq_add_neg A, @right_distrib A] end
                ... = d                   : begin rewrite h, simp [@add_sub_cancel A] end

  theorem mul_neg_one_eq_neg : a * (-1) = -a :=
    have a + a * -1 = 0, from calc
      a + a * -1 = a * 1 + a * -1 : by simp
             ... = a * (1 + -1)   : eq.symm (left_distrib a 1 (-1))
             ... = 0              : by simp,
    symm (neg_eq_of_add_eq_zero this)

  theorem ne_zero_and_ne_zero_of_mul_ne_zero {a b : A} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  begin
    split,
      intro ha, apply h, simp [ha],
    intro hb, apply h, simp [hb]
  end
end

class comm_ring (A : Type uu) extends ring A, comm_semigroup A

@[instance] def comm_ring.to_comm_semiring [s : comm_ring A] : comm_semiring A :=
{ s with
  mul_zero := mul_zero,
  zero_mul := zero_mul }

section
  variables [comm_ring A] (a b c d e : A)

  local attribute [simp] left_distrib right_distrib

  theorem mul_self_sub_mul_self_eq : a * a - b * b = (a + b) * (a - b) :=
  sorry -- by simp [@sub_eq_add_neg A]

  theorem mul_self_sub_one_eq : a * a - 1 = (a + 1) * (a - 1) :=
  sorry -- by simp

  theorem add_mul_self_eq : (a + b) * (a + b) = a*a + 2*a*b + b*b :=
  calc (a + b)*(a + b) = a*a + (1+1)*a*b + b*b : sorry -- by simp
               ...     = a*a + 2*a*b + b*b     : sorry -- by rewrite one_add_one_eq_two

  theorem dvd_add {a b c : A} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  dvd_elim h₁ (λ d hd, dvd_elim h₂ (λ e he, dvd_intro (d + e) (by simp [hd, he])))

  theorem dvd_neg_iff_dvd : (a ∣ -b) ↔ (a ∣ b) :=
  iff.intro
    (suppose a ∣ -b,
      dvd.elim this
        (take c, suppose -b = a * c,
          dvd_intro (-c) (by simp [this^.symm])))
    (suppose a ∣ b,
      dvd.elim this
        (take c, suppose b = a * c,
          dvd_intro (-c) (by simp [this^.symm])))

  theorem dvd_neg_of_dvd : (a ∣ b) → (a ∣ -b) :=
  iff.mpr (dvd_neg_iff_dvd a b)

  theorem dvd_of_dvd_neg : (a ∣ -b) → (a ∣ b) :=
  iff.mp (dvd_neg_iff_dvd a b)

  theorem neg_dvd_iff_dvd : (-a ∣ b) ↔ (a ∣ b) :=
  iff.intro
    (suppose -a ∣ b,
      dvd.elim this
        (take c, suppose b = -a * c,
          dvd_intro (-c) (by simp [this])))
    (suppose a ∣ b,
      dvd.elim this
        (take c, suppose b = a * c,
          dvd_intro (-c) (by simp [this])))

  theorem neg_dvd_of_dvd : a ∣ b → -a ∣ b :=
  iff.mpr (neg_dvd_iff_dvd a b)

  theorem dvd_of_neg_dvd : -a ∣ b → a ∣ b :=
  iff.mp (neg_dvd_iff_dvd a b)

  theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c :=
  dvd_add h₁ (dvd_neg_of_dvd a c h₂)
end

/- integral domains -/

class no_zero_divisors (A : Type uu) extends has_mul A, has_zero A :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀a b, mul a b = zero → a = zero ∨ b = zero)

theorem eq_zero_or_eq_zero_of_mul_eq_zero {A : Type uu} [no_zero_divisors A] {a b : A}
    (h : a * b = 0) :
  a = 0 ∨ b = 0 :=
no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero a b h

theorem eq_zero_of_mul_self_eq_zero {A : Type uu} [no_zero_divisors A] {a : A} (h : a * a = 0) :
  a = 0 :=
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) (assume h', h') (assume h', h')

class integral_domain (A : Type uu) extends comm_ring A, no_zero_divisors A,
    zero_ne_one_class A

section
  variables [s : integral_domain A] (a b c d e : A)
  include s

  theorem mul_ne_zero {a b : A} (h1 : a ≠ 0) (h2 : b ≠ 0) : a * b ≠ 0 :=
  suppose a * b = 0,
  or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this) (assume h3, h1 h3) (assume h4, h2 h4)

  theorem eq_of_mul_eq_mul_right_of_ne_zero {a b c : A} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have b * a - c * a = 0, from (eq_iff_sub_eq_zero _ _)^.mp h,
  have (b - c) * a = 0, by rewrite [mul_sub_right_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this)^.resolve_right ha,
  (eq_iff_sub_eq_zero _ _)^.mpr this

  theorem eq_of_mul_eq_mul_left_of_ne_zero {a b c : A} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, from (eq_iff_sub_eq_zero _ _)^.mp h,
  have a * (b - c) = 0, by rewrite [mul_sub_left_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this)^.resolve_left ha,
  (eq_iff_sub_eq_zero _ _)^.mpr this

  -- TODO: do we want the iff versions?

  theorem eq_zero_of_mul_eq_self_right {a b : A} (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  have b - 1 ≠ 0, from
    suppose b - 1 = 0,
    have b = 1, from eq_of_sub_eq_zero this,
    h₁ this,
  have a * b - a = 0, by simp [h₂, sub_self],
  have a * (b - 1) = 0, begin rewrite [mul_sub_left_distrib, mul_one], apply this end,
    show a = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this)^.resolve_right ‹b - 1 ≠ 0›

  theorem eq_zero_of_mul_eq_self_left {a b : A} (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  eq_zero_of_mul_eq_self_right h₁ (begin rewrite mul_comm at h₂, exact h₂ end)

  theorem mul_self_eq_mul_self_iff (a b : A) : a * a = b * b ↔ a = b ∨ a = -b :=
  sorry
  /-
  iff.intro
    (suppose a * a = b * b,
      have (a - b) * (a + b) = 0,
        by rewrite [mul_comm, -mul_self_sub_mul_self_eq, this, sub_self],
      have a - b = 0 ∨ a + b = 0, from !eq_zero_or_eq_zero_of_mul_eq_zero this,
      or.elim this
        (suppose a - b = 0, or.inl (eq_of_sub_eq_zero this))
        (suppose a + b = 0, or.inr (eq_neg_of_add_eq_zero this)))
    (suppose a = b ∨ a = -b, or.elim this
      (suppose a = b,  by rewrite this)
      (suppose a = -b, by rewrite [this, neg_mul_neg]))
  -/

  theorem mul_self_eq_one_iff (a : A) : a * a = 1 ↔ a = 1 ∨ a = -1 :=
  sorry
  /-
  have a * a = 1 * 1 ↔ a = 1 ∨ a = -1, from mul_self_eq_mul_self_iff a 1,
  by rewrite mul_one at this; exact this
  -/
  -- TODO: c - b * c → c = 0 ∨ b = 1 and variants

  theorem dvd_of_mul_dvd_mul_left {a b c : A} (Ha : a ≠ 0) (Hdvd : (a * b ∣ a * c)) : (b ∣ c) :=
  sorry
  /-
  dvd.elim Hdvd
    (take d,
      suppose a * c = a * b * d,
      have b * d = c, from eq_of_mul_eq_mul_left Ha begin rewrite -mul.assoc, symmetry, exact this end,
      dvd_intro this)
  -/

  theorem dvd_of_mul_dvd_mul_right {a b c : A} (Ha : a ≠ 0) (Hdvd : (b * a ∣ c * a)) : (b ∣ c) :=
  sorry
  /-
  dvd.elim Hdvd
    (take d,
      suppose c * a = b * a * d,
      have b * d * a = c * a, from by rewrite [mul.right_comm, -this],
      have b * d = c, from eq_of_mul_eq_mul_right Ha this,
      dvd_intro this)
  -/
end

/-
namespace norm_num

local attribute bit0 bit1 add1 [reducible]
local attribute right_distrib left_distrib [simp]

theorem mul_zero [mul_zero_class A] (a : A) : a * zero = zero :=
sorry -- by simp

theorem zero_mul [mul_zero_class A] (a : A) : zero * a = zero :=
sorry -- by simp

theorem mul_one [monoid A] (a : A) : a * one = a :=
sorry -- by simp

theorem mul_bit0 [distrib A] (a b : A) : a * (bit0 b) = bit0 (a * b) :=
sorry -- by simp

theorem mul_bit0_helper [distrib A] (a b t : A) (h : a * b = t) : a * (bit0 b) = bit0 t :=
sorry -- by rewrite -H; simp

theorem mul_bit1 [semiring A] (a b : A) : a * (bit1 b) = bit0 (a * b) + a :=
sorry -- by simp

theorem mul_bit1_helper [semiring A] (a b s t : A) (Hs : a * b = s) (Ht : bit0 s + a  = t) :
        a * (bit1 b) = t :=
sorry -- by simp

theorem subst_into_prod [has_mul A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
        (prt : tl * tr = t) :
        l * r = t :=
sorry -- by simp

theorem mk_cong (op : A → A) (a b : A) (h : a = b) : op a = op b :=
sorry -- by simp

theorem neg_add_neg_eq_of_add_add_eq_zero [add_comm_group A] (a b c : A) (h : c + a + b = 0) :
        -a + -b = c :=
sorry
/-
begin
  apply add_neg_eq_of_eq_add,
  apply neg_eq_of_add_eq_zero,
  simp
end
-/

theorem neg_add_neg_helper [add_comm_group A] (a b c : A) (h : a + b = c) : -a + -b = -c :=
sorry -- begin apply iff.mp !neg_eq_neg_iff_eq, simp end

theorem neg_add_pos_eq_of_eq_add [add_comm_group A] (a b c : A) (h : b = c + a) : -a + b = c :=
sorry -- begin apply neg_add_eq_of_eq_add, simp end

theorem neg_add_pos_helper1 [add_comm_group A] (a b c : A) (h : b + c = a) : -a + b = -c :=
sorry -- begin apply neg_add_eq_of_eq_add, apply eq_add_neg_of_add_eq H end

theorem neg_add_pos_helper2 [add_comm_group A] (a b c : A) (h : a + c = b) : -a + b = c :=
sorry -- begin apply neg_add_eq_of_eq_add, rewrite H end

theorem pos_add_neg_helper [add_comm_group A] (a b c : A) (h : b + a = c) : a + b = c :=
sorry -- by simp

theorem sub_eq_add_neg_helper [add_comm_group A] (t₁ t₂ e w₁ w₂: A) (H₁ : t₁ = w₁)
        (H₂ : t₂ = w₂) (h : w₁ + -w₂ = e) : t₁ - t₂ = e :=
sorry -- by simp

theorem pos_add_pos_helper [add_comm_group A] (a b c h₁ h₂ : A) (H₁ : a = h₁) (H₂ : b = h₂)
        (h : h₁ + h₂ = c) : a + b = c :=
sorry -- by simp

theorem subst_into_subtr [add_group A] (l r t : A) (prt : l + -r = t) : l - r = t :=
sorry -- by simp

theorem neg_neg_helper [add_group A] (a b : A) (h : a = -b) : -a = b :=
sorry -- by simp

theorem neg_mul_neg_helper [ring A] (a b c : A) (h : a * b = c) : (-a) * (-b) = c :=
sorry -- by simp

theorem neg_mul_pos_helper [ring A] (a b c : A) (h : a * b = c) : (-a) * b = -c :=
sorry -- by simp

theorem pos_mul_neg_helper [ring A] (a b c : A) (h : a * b = c) : a * (-b) = -c :=
sorry -- by simp

end norm_num

attribute [simp]
  zero_mul mul_zero

attribute [simp]
  neg_mul_eq_neg_mul_symm mul_neg_eq_neg_mul_symm

attribute [simp]
  left_distrib right_distrib
-/
