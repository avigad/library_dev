/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
open eq

universe variable uu
variable {A : Type uu}

/- comm semiring -/

section comm_semiring
  variables [comm_semiring A] (a b c : A)

  @[instance] def comm_semiring_has_dvd : has_dvd A :=
  has_dvd.mk (λ a b, ∃ c, b = a * c)

  -- TODO: this used to not have c explicit, but that seems to be important
  --       for use with tactics, similar to exist.intro
  theorem dvd.intro {a b : A} (c : A) (h : a * c = b) : a ∣ b :=
  exists.intro c h^.symm

  def dvd_of_mul_right_eq := @dvd.intro

  theorem dvd.intro_left {a b : A} (c : A) (h : c * a = b) : a ∣ b :=
  dvd.intro _ (begin rewrite mul_comm at h, apply h end)

  def dvd_of_mul_left_eq := @dvd.intro_left

  theorem exists_eq_mul_right_of_dvd {a b : A} (h : a ∣ b) : ∃ c, b = a * c := h

  theorem dvd.elim {P : Prop} {a b : A} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
  exists.elim H₁ H₂

  theorem exists_eq_mul_left_of_dvd {a b : A} (h : a ∣ b) : ∃ c, b = c * a :=
  dvd.elim h (take c, assume H1 : b = a * c, exists.intro c (eq.trans H1 (mul_comm a c)))

  theorem dvd.elim_left {P : Prop} {a b : A} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
  exists.elim (exists_eq_mul_left_of_dvd h₁) (take c, assume h₃ : b = c * a, h₂ c h₃)

  @[simp] theorem dvd_refl : a ∣ a :=
  dvd.intro 1 (by simp)

  theorem dvd_trans {a b c : A} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  match h₁, h₂ with
  | ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ :=
    ⟨d * e, show c = a * (d * e), by simp [h₃, h₄]⟩
  end

  def dvd.trans := @dvd_trans

  theorem eq_zero_of_zero_dvd {a : A} (h : 0 ∣ a) : a = 0 :=
  dvd.elim h (take c, assume H' : a = 0 * c, eq.trans H' (zero_mul c))

  @[simp] theorem dvd_zero : a ∣ 0 := dvd.intro 0 (by simp)

  @[simp] theorem one_dvd : 1 ∣ a := dvd.intro a (by simp)

  @[simp] theorem dvd_mul_right : a ∣ a * b := dvd.intro b rfl

  @[simp] theorem dvd_mul_left : a ∣ b * a := dvd.intro b (by simp)

  theorem dvd_mul_of_dvd_left {a b : A} (h : a ∣ b) (c : A) : a ∣ b * c :=
  dvd.elim h (λ d h', begin rw [h', mul_assoc], apply dvd_mul_right end)

  theorem dvd_mul_of_dvd_right {a b : A} (h : a ∣ b) (c : A) : a ∣ c * b :=
  begin rw mul_comm, exact dvd_mul_of_dvd_left h _ end

  theorem mul_dvd_mul {a b c d : A} (dvd_ab : a ∣ b) (dvd_cd : c ∣ d) : a * c ∣ b * d :=
  dvd.elim dvd_ab (take e, assume beq,
    dvd.elim dvd_cd (take f, assume deq,
      dvd.intro (e * f) (by simp [beq, deq])))

  theorem mul_dvd_mul_left (a : A) {b c : A} (h : b ∣ c) : a * b ∣ a * c :=
  mul_dvd_mul (dvd_refl a) h

  theorem mul_dvd_mul_right {a b : A} (h : a ∣ b) (c : A) : a * c ∣ b * c :=
  mul_dvd_mul h (dvd_refl c)

  theorem dvd_add {a b c : A} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  dvd.elim h₁ (λ d hd, dvd.elim h₂ (λ e he, dvd.intro (d + e) (by simp [left_distrib, hd, he])))

/-
  -- TODO: this should work, but doesn't.
  -- The function definition system says we don't have well-founded recursion

  theorem mul_dvd_mul' {a b c d : A} (dvd_ab : a ∣ b) (dvd_cd : c ∣ d) : a * c ∣ b * d :=
  match dvd_ab, dvd_cd with
  | ⟨e, (he : b = a * e)⟩, ⟨f, (hf : d = c * f)⟩ :=
    begin subst he, subst hf, apply (@dvd.intro A _ _ _ (e * f)), simp end
  end
-/

  theorem dvd_of_mul_right_dvd {a b c : A} (h : a * b ∣ c) : a ∣ c :=
  dvd.elim h (begin intros d h₁, rw [h₁, mul_assoc], apply dvd_mul_right end)

  theorem dvd_of_mul_left_dvd {a b c : A} (h : a * b ∣ c) : b ∣ c :=
  dvd.elim h (λ d ceq, dvd.intro (a * d) (by simp [ceq]))
end comm_semiring

/- ring -/

section
  variables [ring A] (a b c d e : A)

  theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp
      ... ↔ a * e + c - b * e = d : iff.intro (λ h, begin simp [h] end) (λ h,
                                                    begin simp [h^.symm] end)
      ... ↔ (a - b) * e + c = d   : begin simp [@sub_eq_add_neg A, @right_distrib A] end

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

section
  variables [comm_ring A] {a b c d e : A}

  local attribute [simp] left_distrib right_distrib

  theorem dvd_neg_of_dvd (h : a ∣ b) : (a ∣ -b) :=
  dvd.elim h
    (take c, suppose b = a * c,
      dvd.intro (-c) (by simp [this]))

  theorem dvd_of_dvd_neg (h : a ∣ -b) : (a ∣ b) :=
  let t := dvd_neg_of_dvd h in by rwa neg_neg at t

  theorem dvd_neg_iff_dvd : (a ∣ -b) ↔ (a ∣ b) :=
  ⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

  theorem neg_dvd_of_dvd (h : a ∣ b) : -a ∣ b :=
  dvd.elim h
    (take c, suppose b = a * c,
      dvd.intro (-c) (by simp [this]))

  theorem dvd_of_neg_dvd (h : -a ∣ b) : a ∣ b :=
  let t := neg_dvd_of_dvd h in by rwa neg_neg at t

  theorem neg_dvd_iff_dvd : (-a ∣ b) ↔ (a ∣ b) :=
  ⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

  theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c :=
  dvd_add h₁ (dvd_neg_of_dvd h₂)

  theorem dvd_add_iff_left {a b c : A} (h : a ∣ c) : a ∣ b ↔ a ∣ b + c :=
  ⟨λh₂, dvd_add h₂ h, λH, by note t := dvd_sub H h; rwa add_sub_cancel at t⟩

  theorem dvd_add_iff_right {a b c : A} (h : a ∣ b) : a ∣ c ↔ a ∣ b + c :=
  by rw add_comm; exact dvd_add_iff_left h
end

/- integral domains -/

section
  variables [s : integral_domain A] (a b c d e : A)
  include s

  theorem eq_of_mul_eq_mul_right_of_ne_zero {a b c : A} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have b * a - c * a = 0, by simp [h],
  have (b - c) * a = 0, by rewrite [mul_sub_right_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this)^.resolve_right ha,
  eq_of_sub_eq_zero this

  theorem eq_of_mul_eq_mul_left_of_ne_zero {a b c : A} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, by simp [h],
  have a * (b - c) = 0, by rewrite [mul_sub_left_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this)^.resolve_left ha,
  eq_of_sub_eq_zero this

  -- TODO: do we want the iff versions?

--  theorem dvd_of_mul_dvd_mul_left {a b c : A} (Ha : a ≠ 0) (Hdvd : (a * b ∣ a * c)) : (b ∣ c) :=
--  sorry
  /-
  dvd.elim Hdvd
    (take d,
      suppose a * c = a * b * d,
      have b * d = c, from eq_of_mul_eq_mul_left Ha begin rewrite -mul.assoc, symmetry, exact this end,
      dvd.intro this)
  -/

--  theorem dvd_of_mul_dvd_mul_right {a b c : A} (Ha : a ≠ 0) (Hdvd : (b * a ∣ c * a)) : (b ∣ c) :=
--  sorry
  /-
  dvd.elim Hdvd
    (take d,
      suppose c * a = b * a * d,
      have b * d * a = c * a, from by rewrite [mul.right_comm, -this],
      have b * d = c, from eq_of_mul_eq_mul_right Ha this,
      dvd.intro this)
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
