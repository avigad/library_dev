/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/

-- TODO(Jeremy): these used to be proved by rec_simp. Write a special tactic for these, or
-- get auto or super to do them.

namespace bool

  -- TODO(Jeremy): is this right?
  @[simp] theorem coe_tt : (↑tt : Prop) := dec_trivial

  theorem band_tt (a : bool) : a && tt = a  := begin cases a, repeat { reflexivity } end

  theorem tt_band (a : bool) : tt && a = a  := begin cases a, repeat { reflexivity } end

  theorem band_ff (a : bool) : a && ff = ff := begin cases a, repeat { reflexivity } end

  theorem ff_band (a : bool) : ff && a = ff := begin cases a, repeat { reflexivity } end

  theorem bor_tt (a : bool) : a || tt = tt  := begin cases a, repeat { reflexivity } end

  theorem tt_bor (a : bool) : tt || a = tt  := begin cases a, repeat { reflexivity } end

  theorem bor_ff (a : bool) : a || ff = a   := begin cases a, repeat { reflexivity } end

  theorem ff_bor (a : bool) : ff || a = a   := begin cases a, repeat { reflexivity } end

  attribute [simp] band_tt tt_band band_ff ff_band bor_tt tt_bor bor_ff ff_bor

  theorem band_eq_tt (a b : bool) : (a && b = tt) = (a = tt ∧ b = tt) :=
  begin cases a, repeat { cases b, repeat { simp } } end

  theorem band_eq_ff (a b : bool) : (a && b = ff) = (a = ff ∨ b = ff) :=
  begin cases a, repeat { cases b, repeat { simp } } end

  theorem bor_eq_tt (a b : bool) : (a || b = tt) = (a = tt ∨ b = tt) :=
  begin cases a, repeat { cases b, repeat { simp } } end

  theorem bor_eq_ff (a b : bool) : (a || b = ff) = (a = ff ∧ b = ff) :=
  begin cases a, repeat { cases b, repeat { simp } } end

  theorem dichotomy (b : bool) : b = ff ∨ b = tt :=
  begin cases b, simp, simp end

  @[simp]
  theorem cond_ff {A : Type} (t e : A) : cond ff t e = e :=
  rfl

  @[simp]
  theorem cond_tt {A : Type} (t e : A) : cond tt t e = t :=
  rfl

  theorem eq_tt_of_ne_ff : ∀ {a : bool}, a ≠ ff → a = tt :=
  begin intro a, cases a, simp, simp end

  theorem eq_ff_of_ne_tt : ∀ {a : bool}, a ≠ tt → a = ff :=
  begin intro a, cases a, simp, simp end

  theorem absurd_of_eq_ff_of_eq_tt {B : Prop} {a : bool} (H₁ : a = ff) (H₂ : a = tt) : B :=
  begin cases a, repeat { contradiction } end

  @[simp]
  theorem bor_comm (a b : bool) : a || b = b || a :=
  begin cases a, repeat { cases b, repeat { simp } } end

  @[simp]
  theorem bor_assoc (a b c : bool) : (a || b) || c = a || (b || c) :=
  begin cases a, repeat { cases b, repeat { simp } } end

  @[simp]
  theorem bor_left_comm (a b c : bool) : a || (b || c) = b || (a || c) :=
  begin cases a, repeat { cases b, repeat { simp } } end

  theorem or_of_bor_eq {a b : bool} : a || b = tt → a = tt ∨ b = tt :=
  begin cases a, simp, intro h, simp [h], simp end

  theorem bor_inl {a b : bool} (H : a = tt) : a || b = tt :=
  by simp [H]

  theorem bor_inr {a b : bool} (H : b = tt) : a || b = tt :=
  by simp [H]

  @[simp]
  theorem band_self (a : bool) : a && a = a :=
  begin cases a, repeat { simp } end

  @[simp]
  theorem band_comm (a b : bool) : a && b = b && a :=
  begin cases a, repeat { simp } end

  @[simp]
  theorem band_assoc (a b c : bool) : (a && b) && c = a && (b && c) :=
  begin cases a, repeat { simp } end

  @[simp]
  theorem band_left_comm (a b c : bool) : a && (b && c) = b && (a && c) :=
  begin cases a, repeat { simp } end

  theorem band_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
  begin cases a, simp at H, simp [H] end

  theorem band_intro {a b : bool} (H₁ : a = tt) (H₂ : b = tt) : a && b = tt :=
  begin cases a, repeat { simp [H₁, H₂] }, simp [H₂] end

  theorem band_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
  begin cases a, contradiction, simp at H, exact H end

  @[simp]
  theorem bnot_false : bnot ff = tt :=
  rfl

  @[simp]
  theorem bnot_true : bnot tt = ff :=
  rfl

  @[simp]
  theorem bnot_bnot (a : bool) : bnot (bnot a) = a :=
  by cases a; simp; simp

  theorem eq_tt_of_bnot_eq_ff {a : bool} : bnot a = ff → a = tt :=
  by cases a; simp; simp

  theorem eq_ff_of_bnot_eq_tt {a : bool} : bnot a = tt → a = ff :=
  by cases a; simp; simp

  definition bxor : bool → bool → bool
  | ff ff := ff
  | ff tt := tt
  | tt ff := tt
  | tt tt := ff

  @[simp]
  lemma ff_bxor_ff : bxor ff ff = ff := rfl
  @[simp]
  lemma ff_bxor_tt : bxor ff tt = tt := rfl
  @[simp]
  lemma tt_bxor_ff : bxor tt ff = tt := rfl
  @[simp]
  lemma tt_bxor_tt : bxor tt tt = ff := rfl

  @[simp]
  lemma bxor_self (a : bool) : bxor a a = ff :=
  begin cases a, repeat { simp } end

  @[simp]
  lemma bxor_ff (a : bool) : bxor a ff = a :=
  begin cases a, repeat { simp } end

  @[simp]
  lemma bxor_tt (a : bool) : bxor a tt = bnot a :=
  begin cases a, repeat { simp } end

  @[simp]
  lemma ff_bxor (a : bool) : bxor ff a = a :=
  begin cases a, repeat { simp } end

  @[simp]
  lemma tt_bxor (a : bool) : bxor tt a = bnot a :=
  begin cases a, repeat { simp } end

  @[simp]
  lemma bxor_comm (a b : bool) : bxor a b = bxor b a :=
  begin cases a, repeat { simp } end

  @[simp]
  lemma bxor_assoc (a b c : bool) : bxor (bxor a b) c = bxor a (bxor b c) :=
  begin cases a, repeat { cases b, repeat { simp } } end

  @[simp]
  lemma bxor_left_comm (a b c : bool) : bxor a (bxor b c) = bxor b (bxor a c) :=
  begin cases a, repeat { cases b, repeat { simp } } end
end bool
