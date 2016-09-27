/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

-- TODO: should we make an effort to separate out the classical principles?
-- TODO: in particular, do we want versions of theorems that assume "decidable" as
         a hypothesis?
-- TODO: fix all the names, once we agree on naming conventions
-- TODO: port logic.identities.
-/
open tactic  -- TODO: currently only needed for "intros"

/-
    propositional connectives
-/

section propositional
variables {a b c d : Prop}

/- implies -/

definition imp (a b : Prop) : Prop := a → b

theorem imp.id (H : a) : a := H

theorem imp.intro (H : a) (H₂ : b) : a := H

theorem imp.mp (H : a) (H₂ : a → b) : b :=
H₂ H

theorem imp.syl (H : a → b) (H₂ : c → a) (Hc : c) : b :=
H (H₂ Hc)

theorem imp.left (H : a → b) (H₂ : b → c) (Ha : a) : c :=
H₂ (H Ha)

theorem imp_true (a : Prop) : (a → true) ↔ true :=
iff_true_intro (imp.intro trivial)

theorem true_imp (a : Prop) : (true → a) ↔ a :=
iff.intro (assume H, H trivial) imp.intro

theorem imp_false (a : Prop) : (a → false) ↔ ¬ a := iff.rfl

theorem false_imp (a : Prop) : (false → a) ↔ true :=
iff_true_intro false.elim

/- not -/

theorem {u} not.elim {A : Type u} (H1 : ¬a) (H2 : a) : A := absurd H2 H1

theorem not.mto {a b : Prop} : (a → b) → ¬b → ¬a := imp.left

theorem not_imp_not_of_imp {a b : Prop} : (a → b) → ¬b → ¬a := not.mto

theorem not_not_of_not_implies : ¬(a → b) → ¬¬a :=
not.mto not.elim

theorem not_of_not_implies : ¬(a → b) → ¬b :=
not.mto imp.intro

theorem not_not_em : ¬¬(a ∨ ¬a) :=
assume not_em : ¬(a ∨ ¬a),
not_em (or.inr (not.mto or.inl not_em))

theorem not_iff_not (H : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (not.mto (iff.mpr H)) (not.mto (iff.mp H))

/- and -/

definition not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) :=
not.mto and.left

definition not_and_of_not_right (a : Prop) {b : Prop} : ¬b →  ¬(a ∧ b) :=
not.mto and.right

theorem and.imp_left (H : a → b) : a ∧ c → b ∧ c :=
and.imp H imp.id

theorem and.imp_right (H : a → b) : c ∧ a → c ∧ b :=
and.imp imp.id H

theorem and_of_and_of_imp_of_imp (H₁ : a ∧ b) (H₂ : a → c) (H₃ : b → d) : c ∧ d :=
and.imp H₂ H₃ H₁

theorem and_of_and_of_imp_left (H₁ : a ∧ c) (H : a → b) : b ∧ c :=
and.imp_left H H₁

theorem and_of_and_of_imp_right (H₁ : c ∧ a) (H : a → b) : c ∧ b :=
and.imp_right H H₁

theorem and_imp_iff (a b c : Prop) : (a ∧ b → c) ↔ (a → b → c) :=
iff.intro (λH a b, H (and.intro a b)) and.rec

theorem and_imp_eq (a b c : Prop) : (a ∧ b → c) = (a → b → c) :=
propext (and_imp_iff a b c)

/- or -/

theorem or_of_or_of_imp_of_imp (H₁ : a ∨ b) (H₂ : a → c) (H₃ : b → d) : c ∨ d :=
or.imp H₂ H₃ H₁

theorem or_of_or_of_imp_left (H₁ : a ∨ c) (H : a → b) : b ∨ c :=
or.imp_left H H₁

theorem or_of_or_of_imp_right (H₁ : c ∨ a) (H : a → b) : c ∨ b :=
or.imp_right H H₁

theorem or.elim3 (H : a ∨ b ∨ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
or.elim H Ha (assume H₂, or.elim H₂ Hb Hc)

theorem or_resolve_right (H₁ : a ∨ b) (H₂ : ¬a) : b :=
or.elim H₁ (not.elim H₂) imp.id

theorem or_resolve_left (H₁ : a ∨ b) : ¬b → a :=
or_resolve_right (or.swap H₁)

theorem or.imp_distrib : ((a ∨ b) → c) ↔ ((a → c) ∧ (b → c)) :=
iff.intro
  (λH, and.intro (imp.syl H or.inl) (imp.syl H or.inr))
  (and.rec or.rec)

theorem or_iff_right_of_imp {a b : Prop} (Ha : a → b) : (a ∨ b) ↔ b :=
iff.intro (or.rec Ha imp.id) or.inr

theorem or_iff_left_of_imp {a b : Prop} (Hb : b → a) : (a ∨ b) ↔ a :=
iff.intro (or.rec imp.id Hb) or.inl

theorem or_iff_or (H1 : a ↔ c) (H2 : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
iff.intro (or.imp (iff.mp H1) (iff.mp H2)) (or.imp (iff.mpr H1) (iff.mpr H2))

/- distributivity -/

theorem and_distrib (a b c : Prop) : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
iff.intro
  (and.rec (λH, or.imp (and.intro H) (and.intro H)))
  (or.rec (and.imp_right or.inl) (and.imp_right or.inr))

theorem and_distrib_right (a b c : Prop) : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) :=
iff.trans (iff.trans and.comm (and_distrib c a b)) (or_iff_or and.comm and.comm)

theorem or_distrib (a b c : Prop) : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
iff.intro
  (or.rec (λH, and.intro (or.inl H) (or.inl H)) (and.imp or.inr or.inr))
  (and.rec (or.rec (imp.syl imp.intro or.inl) (imp.syl or.imp_right and.intro)))

theorem or_distrib_right (a b c : Prop) : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
iff.trans (iff.trans or.comm (or_distrib c a b)) (and_congr or.comm or.comm)

/- iff -/

definition iff.def : (a ↔ b) = ((a → b) ∧ (b → a)) := rfl

theorem forall_imp_forall {A : Type} {P Q : A → Prop} (H : ∀a, (P a → Q a)) (p : ∀a, P a) (a : A)
  : Q a :=
(H a) (p a)

theorem forall_iff_forall {A : Type} {P Q : A → Prop} (H : ∀a, (P a ↔ Q a))
  : (∀a, P a) ↔ (∀a, Q a) :=
iff.intro (λp a, iff.elim_left (H a) (p a)) (λq a, iff.elim_right (H a) (q a))

theorem imp_iff {P : Prop} (Q : Prop) (p : P) : (P → Q) ↔ Q :=
iff.intro (λf, f p) imp.intro

end propositional


/- quantifiers -/

theorem exists_imp_distrib {A : Type} {b : Prop} {p : A → Prop} :
  ((∃ a : A, p a) → b) ↔ (∀ a : A, p a → b) :=
iff.intro (λ e x h, e ⟨x, h⟩) Exists.rec

theorem forall_iff_not_exists {A : Type} {p : A → Prop} :
  (¬ ∃ a : A, p a) ↔ ∀ a : A, ¬ p a :=
exists_imp_distrib


/- bounded quantifiers -/

lemma bforall_congr {A : Type} {s : set A} {p q : A → Prop} (H : ∀ x ∈ s, p x ↔ q x) :
  (∀ x ∈ s, p x) = (∀ x ∈ s, q x) :=
begin
  apply propext,
  apply forall_congr,
  intro x,
  apply imp_congr_right,
  apply H
end

lemma bexists_congr {A : Type} {s : set A} {p q : A → Prop} (h : ∀ x ∈ s, p x ↔ q x) :
  (∃ x ∈ s, p x) = (∃ x ∈ s, q x) :=
begin
  apply propext,
  apply exists_congr,
  intros,
  apply exists_congr,
  apply h
end

-- TODO: in the old library, these next two assumed [decidable a]
theorem not_and_iff_not_or_not (a b : Prop) :
  ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
sorry

theorem imp_iff_not_or (a b : Prop) [Da : decidable a] : (a → b) ↔ ¬a ∨ b :=
sorry

section
  open classical

  -- TODO: wait for better support for rewrite
  lemma not_bounded_exists {A : Type} {s : set A} {p : A → Prop} :
    (¬ (∃ x ∈ s, p x)) = (∀ x ∈ s, ¬ p x) :=
  sorry
/-
  begin
    rewrite forall_iff_not_exists,
    apply propext,
    apply forall_congr,
    intro x,
    rewrite forall_iff_not_exists,
    rewrite not_and_iff_not_or_not,
    rewrite imp_iff_not_or
  end
-/

  lemma not_bounded_forall {A : Type} {s : set A} {p : A → Prop} :
    (¬ (∀ x ∈ s, p x)) = (∃ x ∈ s, ¬ p x) :=
  sorry
/-
  calc (¬ (∀ x ∈ s, p x)) = ¬ ¬ (∃ x ∈ s, ¬ p x) :
    begin
      rewrite not_bounded_exists,
      apply (congr_arg not),
      apply bounded_forall_congr,
      intros x H,
      rewrite not_not_iff
    end
    ... = (∃ x ∈ S, ¬ P x) : by (rewrite not_not_iff)
-/

end
