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

  theorem le_max_left_iff_true (a b : α) : a ≤ max a b ↔ true :=
  iff_true_intro (le_max_left a b)

  theorem le_max_right_iff_true (a b : α) : b ≤ max a b ↔ true :=
  iff_true_intro (le_max_right a b)

  theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
  right_comm min min_comm min_assoc a b c

  theorem max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
  left_comm max max_comm max_assoc a b c

  theorem max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
  right_comm max max_comm max_assoc a b c
end

/- order instances -/

attribute [instance]
definition weak_order_Prop : weak_order Prop :=
{ le           := λx y, x → y,
  le_refl      := λx, id,
  le_trans     := λa b c h1 h2 x, h2 (h1 x),
  le_antisymm  := λf g h1 h2, propext (iff.intro h1 h2)
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
