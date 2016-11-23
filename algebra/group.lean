/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures.
-/
import ..logic.todo -- ..automation.auto.auto use logic.todo, get rid of duplicate names

universe variable uu
variable {A : Type uu}

section group
  variable [group A]

  variable (A)
  theorem left_inverse_inv : function.left_inverse (λ a : A, a⁻¹) (λ a, a⁻¹) :=
  take a, inv_inv a
  variable {A}

  theorem inv_inj {a b : A} (h : a⁻¹ = b⁻¹) : a = b :=
  have a = a⁻¹⁻¹, by simp,
  begin rewrite this, apply inv_eq_of_mul_eq_one, simp [h] end

  theorem inv_eq_inv_iff_eq (a b : A) : a⁻¹ = b⁻¹ ↔ a = b :=
  iff_intro inv_inj (begin intro h, simp [h] end)

  theorem inv_eq_one_iff_eq_one (a : A) : a⁻¹ = 1 ↔ a = 1 :=
  have a⁻¹ = 1⁻¹ ↔ a = 1, from inv_eq_inv_iff_eq a 1,
  begin rewrite this^.symm, simp end

  theorem eq_one_of_inv_eq_one (a : A) : a⁻¹ = 1 → a = 1 :=
  iff.mp (inv_eq_one_iff_eq_one a)

  theorem eq_inv_of_eq_inv {a b : A} (h : a = b⁻¹) : b = a⁻¹ :=
  by simp [h]

  theorem eq_inv_iff_eq_inv (a b : A) : a = b⁻¹ ↔ b = a⁻¹ :=
  iff.intro eq_inv_of_eq_inv eq_inv_of_eq_inv

  theorem eq_inv_of_mul_eq_one {a b : A} (H : a * b = 1) : a = b⁻¹ :=
  have a⁻¹ = b, from inv_eq_of_mul_eq_one H,
  begin rewrite this^.symm, simp end

  @[simp] theorem mul_inv_cancel_left (a b : A) : a * (a⁻¹ * b) = b :=
  begin rewrite -mul_assoc, simp end

  @[simp] theorem mul_inv_cancel_right (a b : A) : a * b * b⁻¹ = a :=
  begin rewrite mul_assoc, simp end

  @[simp] theorem mul_inv (a b : A) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  inv_eq_of_mul_eq_one (by simp)

  theorem eq_of_mul_inv_eq_one {a b : A} (H : a * b⁻¹ = 1) : a = b :=
  calc
    a    = a * b⁻¹ * b : by simp
     ... = b           : begin rewrite H, simp end


  --TODO: with luck, we can delete all these soon
  theorem eq_mul_inv_of_mul_eq {a b c : A} (H : a * c = b) : a = b * c⁻¹ :=
  begin subst H, simp end

  theorem eq_inv_mul_of_mul_eq {a b c : A} (H : b * a = c) : a = b⁻¹ * c :=
  begin subst H, simp end

  theorem inv_mul_eq_of_eq_mul {a b c : A} (H : b = a * c) : a⁻¹ * b = c :=
  begin subst H, simp end

  theorem mul_inv_eq_of_eq_mul {a b c : A} (H : a = c * b) : a * b⁻¹ = c :=
  begin subst H, simp end

  theorem eq_mul_of_mul_inv_eq {a b c : A} (H : a * c⁻¹ = b) : a = b * c :=
  begin subst H, simp end

  theorem eq_mul_of_inv_mul_eq {a b c : A} (H : b⁻¹ * a = c) : a = b * c :=
  begin subst H, simp end

  theorem mul_eq_of_eq_inv_mul {a b c : A} (H : b = a⁻¹ * c) : a * b = c :=
  begin subst H, simp end

  theorem mul_eq_of_eq_mul_inv {a b c : A} (H : a = c * b⁻¹) : a * b = c :=
  begin subst H, simp end

  theorem mul_eq_iff_eq_inv_mul (a b c : A) : a * b = c ↔ b = a⁻¹ * c :=
  iff.intro eq_inv_mul_of_mul_eq mul_eq_of_eq_inv_mul

  theorem mul_eq_iff_eq_mul_inv (a b c : A) : a * b = c ↔ a = c * b⁻¹ :=
  iff.intro eq_mul_inv_of_mul_eq mul_eq_of_eq_mul_inv
end group

/- transport versions to additive -/

-- TODO: `` notation doesn't seem to detect errors

run_command do monad.mapm'
    (λ p : name × name, transport_to_additive p.1 p.2)
    [(``mul_left_cancel, `add_left_cancel),
     (``mul_right_cancel, `add_right_cancel),
     (``inv_mul_cancel_left, `neg_add_cancel_left),
     (``inv_mul_cancel_right, `neg_add_cancel_right),
     (``inv_eq_of_mul_eq_one, `neg_eq_of_add_eq_zero),
     (``one_inv, `zero_inv),
     (``inv_inv, `neg_neg),
     (``left_inverse_inv, `left_inverse_neg),
     (``inv_inj, `neg_inj),
     (``inv_eq_inv_iff_eq, `neg_eq_neg_iff_eq),
     (``inv_eq_one_iff_eq_one, `neg_eq_zero_iff_eq_zero),
     (``eq_one_of_inv_eq_one, `eq_zero_of_neg_eq_zero),
     (``eq_inv_of_eq_inv, `eq_neg_of_eq_neg),
     (``eq_inv_iff_eq_inv, `eq_neg_iff_eq_neg),
     (``eq_inv_of_mul_eq_one, `eq_neg_of_add_eq_zero),
     (``mul_right_inv, `add_right_inv),
     (``mul_inv_cancel_left, `add_neg_cancel_left),
     (``mul_inv_cancel_right, `add_neg_cancel_right),
     (``mul_inv, `neg_add),
     (``eq_of_mul_inv_eq_one, `eq_of_add_neg_eq_zero),
     (``eq_mul_inv_of_mul_eq, `eq_add_neg_of_add_eq),
     (``eq_inv_mul_of_mul_eq, `eq_neg_add_of_add_eq),
     (``inv_mul_eq_of_eq_mul, `neg_add_eq_of_eq_add),
     (``mul_inv_eq_of_eq_mul, `add_neg_eq_of_eq_add),
     (``eq_mul_of_mul_inv_eq, `eq_add_of_add_neg_eq),
     (``mul_eq_of_eq_inv_mul, `add_eq_of_eq_neg_add),
     (``mul_eq_of_eq_mul_inv, `add_eq_of_eq_add_neg),
     (``mul_eq_iff_eq_inv_mul, `add_eq_iff_eq_neg_add),
     (``mul_eq_iff_eq_mul_inv, `add_eq_iff_eq_add_neg),
     (``group.to_left_cancel_semigroup, `add_group.to_left_cancel_add_semigroup),
     (``group.to_right_cancel_semigroup, `add_group.to_right_cancel_add_semigroup)
     -- (``mul_eq_one_of_mul_eq_one, `add_eq_zero_of_add_eq_zero)   not needed for commutative groups
     -- (``muleq_one_iff_mul_eq_one, `add_eq_zero_iff_add_eq_zero)
]

section add_group
  variable [add_group A]

--  attribute [reducible]
--  protected definition algebra.sub (a b : A) : A := a + -b

  @[instance] def add_group_has_sub : has_sub A :=
  has_sub.mk (λ a b, a + -b)

  theorem sub_eq_add_neg (a b : A) : a - b = a + -b := rfl

  local attribute [simp] sub_eq_add_neg

  -- TODO: maybe none of these are necessary any more...
  -- Or mabe add_group_has_sub *shouldn't* be a simp rule, and these should be?
  theorem sub_self (a : A) : a - a = 0 := by simp

  theorem sub_add_cancel (a b : A) : a - b + b = a := by simp

  theorem add_sub_cancel (a b : A) : a + b - b = a := by simp

  theorem add_sub_assoc (a b c : A) : a + b - c = a + (b - c) := by simp

  theorem eq_of_sub_eq_zero {a b : A} (H : a - b = 0) : a = b :=
  eq_of_add_neg_eq_zero H

  theorem eq_iff_sub_eq_zero (a b : A) : a = b ↔ a - b = 0 :=
  iff.intro (assume h, by simp [h]) (assume h, eq_of_sub_eq_zero h)

  theorem zero_sub (a : A) : 0 - a = -a := by simp

  theorem sub_zero (a : A) : a - 0 = a := by simp

  theorem sub_neg_eq_add (a b : A) : a - (-b) = a + b :=
  by simp

  theorem neg_sub (a b : A) : -(a - b) = b - a :=
  by simp

  theorem add_sub (a b c : A) : a + (b - c) = a + b - c :=
  by simp

  theorem sub_add_eq_sub_sub_swap (a b c : A) : a - (b + c) = a - c - b :=
  by simp

  theorem sub_eq_iff_eq_add (a b c : A) : a - b = c ↔ a = c + b :=
  iff.intro (assume H, eq_add_of_add_neg_eq H) (assume H, add_neg_eq_of_eq_add H)

  theorem eq_sub_iff_add_eq (a b c : A) : a = b - c ↔ a + c = b :=
  iff.intro (assume H, add_eq_of_eq_add_neg H) (assume H, eq_add_neg_of_add_eq H)

  theorem eq_iff_eq_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a = b ↔ c = d :=
  calc
    a = b ↔ a - b = 0   : eq_iff_sub_eq_zero a b
      ... = (c - d = 0) : by rewrite H
      ... ↔ c = d       : iff.symm (eq_iff_sub_eq_zero c d)

  theorem eq_sub_of_add_eq {a b c : A} (H : a + c = b) : a = b - c :=
  begin rewrite -H, simp end

  theorem sub_eq_of_eq_add {a b c : A} (H : a = c + b) : a - b = c :=
  begin rewrite H, simp end

  theorem eq_add_of_sub_eq {a b c : A} (H : a - c = b) : a = b + c :=
  begin rewrite -H, simp end

  theorem add_eq_of_eq_sub {a b c : A} (H : a = c - b) : a + b = c :=
  begin rewrite H, simp end

  theorem left_inverse_sub_add_left (c : A) : function.left_inverse (λ x, x - c) (λ x, x + c) :=
  take x, add_sub_cancel x c

  theorem left_inverse_add_left_sub (c : A) : function.left_inverse (λ x, x + c) (λ x, x - c) :=
  take x, sub_add_cancel x c

  theorem left_inverse_add_right_neg_add (c : A) :
      function.left_inverse (λ x, c + x) (λ x, - c + x) :=
  take x, add_neg_cancel_left c x

  theorem left_inverse_neg_add_add_right (c : A) :
      function.left_inverse (λ x, - c + x) (λ x, c + x) :=
  take x, neg_add_cancel_left c x
end add_group

section add_comm_group
  variable [s : add_comm_group A]
  include s

  local attribute [simp] sub_eq_add_neg

  theorem sub_add_eq_sub_sub (a b c : A) : a - (b + c) = a - b - c :=
  by simp

  theorem neg_add_eq_sub (a b : A) : -a + b = b - a :=
  by simp

  -- TODO: this doesn't work in a begin ... end block -- can't find instance
  theorem neg_add' (a b : A) : -(a + b) = -a + -b :=
  eq_of_sub_eq_zero (by simp)

  theorem sub_add_eq_add_sub (a b c : A) : a - b + c = a + c - b :=
  by simp

  theorem sub_sub (a b c : A) : a - b - c = a - (b + c) :=
  by simp

  theorem add_sub_add_left_eq_sub (a b c : A) : (c + a) - (c + b) = a - b :=
  by simp

  theorem eq_sub_of_add_eq' {a b c : A} (H : c + a = b) : a = b - c :=
  begin rewrite -H, simp end

  theorem sub_eq_of_eq_add' {a b c : A} (H : a = b + c) : a - b = c :=
  begin rewrite H, simp end

  theorem eq_add_of_sub_eq' {a b c : A} (H : a - b = c) : a = b + c :=
  begin rewrite -H, simp end

  theorem add_eq_of_eq_sub' {a b c : A} (H : b = c - a) : a + b = c :=
  begin rewrite H, simp, rewrite [add_comm c, add_neg_cancel_left] end

  theorem sub_sub_self (a b : A) : a - (a - b) = b :=
  begin simp, rewrite [add_comm b, add_neg_cancel_left] end

  theorem add_sub_comm (a b c d : A) : a + b - (c + d) = (a - c) + (b - d) :=
  by simp

  theorem sub_eq_sub_add_sub (a b c : A) : a - b = c - b + (a - c) :=
  by simp

  theorem neg_neg_sub_neg (a b : A) : - (-a - -b) = a - b :=
  by simp
end add_comm_group


/-
namespace norm_num
reveal add.assoc

definition add1 [has_add A] [has_one A] (a : A) : A := add a one

local attribute add1 bit0 bit1 [reducible]

theorem add_comm_four [add_comm_semigroup A] (a b : A) : a + a + (b + b) = (a + b) + (a + b) :=
sorry -- by simp

theorem add_comm_middle [add_comm_semigroup A] (a b c : A) : a + b + c = a + c + b :=
sorry -- by simp

theorem bit0_add_bit0 [add_comm_semigroup A] (a b : A) : bit0 a + bit0 b = bit0 (a + b) :=
sorry -- by simp

theorem bit0_add_bit0_helper [add_comm_semigroup A] (a b t : A) (H : a + b = t) :
        bit0 a + bit0 b = bit0 t :=
sorry -- by rewrite -H; simp

theorem bit1_add_bit0 [add_comm_semigroup A] [has_one A] (a b : A) :
        bit1 a + bit0 b = bit1 (a + b) :=
sorry -- by simp

theorem bit1_add_bit0_helper [add_comm_semigroup A] [has_one A] (a b t : A)
        (H : a + b = t) : bit1 a + bit0 b = bit1 t :=
sorry -- by rewrite -H; simp

theorem bit0_add_bit1 [add_comm_semigroup A] [has_one A] (a b : A) :
        bit0 a + bit1 b = bit1 (a + b) :=
sorry -- by simp

theorem bit0_add_bit1_helper [add_comm_semigroup A] [has_one A] (a b t : A)
        (H : a + b = t) : bit0 a + bit1 b = bit1 t :=
sorry -- by rewrite -H; simp

theorem bit1_add_bit1 [add_comm_semigroup A] [has_one A] (a b : A) :
        bit1 a + bit1 b = bit0 (add1 (a + b)) :=
sorry -- by simp

theorem bit1_add_bit1_helper [add_comm_semigroup A] [has_one A] (a b t s: A)
        (H : (a + b) = t) (H2 : add1 t = s) : bit1 a + bit1 b = bit0 s :=
sorry -- by inst_simp

theorem bin_add_zero [add_monoid A] (a : A) : a + zero = a :=
sorry -- by simp

theorem bin_zero_add [add_monoid A] (a : A) : zero + a = a :=
sorry -- by simp

theorem one_add_bit0 [add_comm_semigroup A] [has_one A] (a : A) : one + bit0 a = bit1 a :=
sorry -- by simp

theorem bit0_add_one [has_add A] [has_one A] (a : A) : bit0 a + one = bit1 a :=
rfl

theorem bit1_add_one [has_add A] [has_one A] (a : A) : bit1 a + one = add1 (bit1 a) :=
rfl

theorem bit1_add_one_helper [has_add A] [has_one A] (a t : A) (H : add1 (bit1 a) = t) :
        bit1 a + one = t :=
sorry -- by inst_simp

theorem one_add_bit1 [add_comm_semigroup A] [has_one A] (a : A) : one + bit1 a = add1 (bit1 a) :=
sorry -- by simp

theorem one_add_bit1_helper [add_comm_semigroup A] [has_one A] (a t : A)
        (H : add1 (bit1 a) = t) : one + bit1 a = t :=
sorry -- by inst_simp

theorem add1_bit0 [has_add A] [has_one A] (a : A) : add1 (bit0 a) = bit1 a :=
rfl

theorem add1_bit1 [add_comm_semigroup A] [has_one A] (a : A) :
        add1 (bit1 a) = bit0 (add1 a) :=
sorry -- by simp

theorem add1_bit1_helper [add_comm_semigroup A] [has_one A] (a t : A) (H : add1 a = t) :
        add1 (bit1 a) = bit0 t :=
sorry -- by inst_simp

theorem add1_one [has_add A] [has_one A] : add1 (one : A) = bit0 one :=
rfl

theorem add1_zero [add_monoid A] [has_one A] : add1 (zero : A) = one :=
sorry -- by simp

theorem one_add_one [has_add A] [has_one A] : (one : A) + one = bit0 one :=
rfl

theorem subst_into_sum [has_add A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
        (prt : tl + tr = t) : l + r = t :=
sorry -- by simp

theorem neg_zero_helper [add_group A] (a : A) (H : a = 0) : - a = 0 :=
sorry -- by simp

end norm_num

attribute [simp]
  zero_add add_zero one_mul mul_one

attribute [simp]
  neg_neg sub_eq_add_neg

attribute [simp]
  add.assoc add.comm add.left_comm
  mul.left_comm mul.comm mul.assoc
-/
