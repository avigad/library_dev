/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
open eq function

universe variable uu
variables {α : Type uu}

section
  variable [decidable_linear_order α]
  variables {a b c d : α}
  open decidable

  definition min (a b : α) : α := if a ≤ b then a else b
  definition max (a b : α) : α := if a ≤ b then b else a

  /- these show min and max form a lattice -/

  theorem min_le_left (a b : α) : min a b ≤ a :=
  by_cases
    (assume h : a ≤ b, begin unfold min, rewrite [if_pos h], apply le_refl end)
    (assume h : ¬ a ≤ b,
      begin unfold min, rewrite  [if_neg h], apply le_of_lt (lt_of_not_ge h) end)

  theorem min_le_right (a b : α) : min a b ≤ b :=
  by_cases
    (assume h : a ≤ b, begin unfold min, rewrite [if_pos h], apply h end)
    (assume h : ¬ a ≤ b, begin unfold min, rewrite [if_neg h], apply le_refl end)

  theorem le_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b :=
  by_cases
    (assume h : a ≤ b, begin unfold min, rewrite [if_pos h], apply h₁ end)
    (assume h : ¬ a ≤ b, begin unfold min, rewrite [if_neg h], apply h₂ end)

  theorem le_max_left (a b : α) : a ≤ max a b :=
  by_cases
    (assume h : a ≤ b, begin unfold max, rewrite [if_pos h], apply h end)
    (assume h : ¬ a ≤ b, begin unfold max, rewrite [if_neg h], apply le_refl end)

  theorem le_max_right (a b : α) : b ≤ max a b :=
  by_cases
    (assume h : a ≤ b, begin unfold max, rewrite [if_pos h], apply le_refl end)
    (assume h : ¬ a ≤ b, begin unfold max, rewrite [if_neg h], apply le_of_lt (lt_of_not_ge h) end)

  theorem max_le {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c :=
  by_cases
    (assume h : a ≤ b, begin unfold max, rewrite [if_pos h], apply h₂ end)
    (assume h : ¬ a ≤ b, begin unfold max, rewrite [if_neg h], apply h₁ end)

  theorem le_max_left_iff_true (a b : α) : a ≤ max a b ↔ true :=
  iff_true_intro (le_max_left a b)

  theorem le_max_right_iff_true (a b : α) : b ≤ max a b ↔ true :=
  iff_true_intro (le_max_right a b)

  /- these are also proved for lattices, but with inf and sup in place of min and max -/

  theorem eq_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀{d}, d ≤ a → d ≤ b → d ≤ c) :
    c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

  theorem min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) (λ c h₁ h₂, le_min h₂ h₁)

  theorem min_assoc (a b c : α) : min (min a b) c = min a (min b c) :=
  begin
    apply eq_min,
    { apply le_trans, apply min_le_left, apply min_le_left },
    { apply le_min, apply le_trans, apply min_le_left, apply min_le_right, apply min_le_right },
    { intros d h₁ h₂, apply le_min, apply le_min h₁, apply le_trans h₂, apply min_le_left,
      apply le_trans h₂, apply min_le_right }
  end

  theorem min_left_comm (a b c : α) : min a (min b c) = min b (min a c) :=
  left_comm min min_comm min_assoc a b c

  theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
  right_comm min min_comm min_assoc a b c

  theorem min_self (a : α) : min a a = a :=
  begin apply eq.symm, apply eq_min (le_refl a) (le_refl _), intros, assumption end

  theorem min_eq_left {a b : α} (h : a ≤ b) : min a b = a :=
  begin apply eq.symm, apply eq_min (le_refl _) h, intros, assumption end

  theorem min_eq_right {a b : α} (h : b ≤ a) : min a b = b :=
  eq.subst (min_comm b a) (min_eq_left h)

  theorem eq_max {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀{d}, a ≤ d → b ≤ d → c ≤ d) :
    c = max a b :=
  le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)

  theorem max_comm (a b : α) : max a b = max b a :=
  eq_max (le_max_right a b) (le_max_left a b) (λ c h₁ h₂, max_le h₂ h₁)

  theorem max_assoc (a b c : α) : max (max a b) c = max a (max b c) :=
  begin
    apply eq_max,
    { apply le_trans, apply le_max_left a b, apply le_max_left },
    { apply max_le, apply le_trans, apply le_max_right a b, apply le_max_left, apply le_max_right },
    { intros d h₁ h₂, apply max_le, apply max_le h₁, apply le_trans (le_max_left _ _) h₂,
      apply le_trans (le_max_right _ _) h₂}
  end

  theorem max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
  left_comm max max_comm max_assoc a b c

  theorem max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
  right_comm max max_comm max_assoc a b c

  theorem max_self (a : α) : max a a = a :=
  begin apply eq.symm, apply eq_max (le_refl a) (le_refl _), intros, assumption end

  theorem max_eq_left {a b : α} (h : b ≤ a) : max a b = a :=
  begin apply eq.symm, apply eq_max (le_refl _) h, intros, assumption end

  theorem max_eq_right {a b : α} (h : a ≤ b) : max a b = b :=
  eq.subst (max_comm b a) (max_eq_left h)

  /- these rely on lt_of_lt -/

  theorem min_eq_left_of_lt {a b : α} (h : a < b) : min a b = a :=
  min_eq_left (le_of_lt h)

  theorem min_eq_right_of_lt {a b : α} (h : b < a) : min a b = b :=
  min_eq_right (le_of_lt h)

  theorem max_eq_left_of_lt {a b : α} (h : b < a) : max a b = a :=
  max_eq_left (le_of_lt h)

  theorem max_eq_right_of_lt {a b : α} (h : a < b) : max a b = b :=
  max_eq_right (le_of_lt h)

  /- these use the fact that it is a linear ordering -/

  theorem lt_min {a b c : α} (h₁ : a < b) (h₂ : a < c) : a < min b c :=
  or.elim (le_or_gt b c)
    (assume h : b ≤ c, begin rewrite (min_eq_left h), apply h₁ end)
    (assume h : b > c, begin rewrite (min_eq_right_of_lt h), apply h₂ end)

  theorem max_lt {a b c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c :=
  or.elim (le_or_gt a b)
    (assume h : a ≤ b, begin rewrite (max_eq_right h), apply h₂ end)
    (assume h : a > b, begin rewrite (max_eq_left_of_lt h), apply h₁ end)
end

/- order instances -/

attribute [instance]
definition weak_order_Prop : weak_order Prop :=
{ le           := λx y, x → y,
  le_refl      := λx, id,
  le_trans     := λa b c h1 h2 x, h2 (h1 x),
  le_antisymm  := λf g h1 h2, propext (and.intro h1 h2)
}

attribute [instance]
definition weak_order_fun (α B : Type) [weak_order B] : weak_order (α → B) :=
{ le := λx y, ∀b, x b ≤ y b,
  le_refl := λf b, le_refl (f b),
  le_trans := λf g h h1 h2 b, le_trans (h1 b) (h2 b),
  le_antisymm := λf g h1 h2, funext (λb, le_antisymm (h1 b) (h2 b))
}

definition weak_order_dual {α : Type} (wo : weak_order α) : weak_order α :=
{ le := λx y, y ≤ x,
  le_refl := le_refl,
  le_trans := take a b c h₁ h₂, le_trans h₂ h₁,
  le_antisymm := take a b h₁ h₂, le_antisymm h₂ h₁ }

lemma le_dual_eq_le {α : Type} (wo : weak_order α) (a b : α) :
  @le _ (@weak_order.to_has_le _ (weak_order_dual wo)) a b =
  @le _ (@weak_order.to_has_le _ wo) b a :=
rfl
