/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

-- TODO: port logic.identities.
-/
import .todo
open tactic  -- TODO: currently only needed for "intros"

/-
    propositional connectives
-/

section propositional
variables {a b c d : Prop}

/- implies -/

theorem implies_self (h : a) : a := h

theorem implies_intro (h : a) (h₂ : b) : a := h

theorem implies_true_iff (a : Prop) : (a → true) ↔ true :=
iff_true_intro (implies_intro trivial)

theorem true_implies_iff (a : Prop) : (true → a) ↔ a :=
iff.intro (assume H, H trivial) implies_intro

theorem implies_false_iff (a : Prop) : (a → false) ↔ ¬ a := iff.rfl

theorem false_implies_iff (a : Prop) : (false → a) ↔ true :=
iff_true_intro false.elim

/- not -/

theorem {u} not_elim {A : Type u} (H1 : ¬a) (H2 : a) : A := absurd H2 H1

theorem not_not_of_not_implies : ¬(a → b) → ¬¬a :=
contrapos not_elim

theorem not_of_not_implies : ¬(a → b) → ¬b :=
contrapos implies_intro

theorem not_iff_not (H : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (contrapos (iff.mpr H)) (contrapos (iff.mp H))

/- and -/

definition not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) :=
contrapos and.left

definition not_and_of_not_right (a : Prop) {b : Prop} : ¬b →  ¬(a ∧ b) :=
contrapos and.right

theorem and_implies_left (H : a → b) : a ∧ c → b ∧ c :=
and_implies H implies_self

theorem and_implies_right (H : a → b) : c ∧ a → c ∧ b :=
and_implies implies_self H

theorem and_of_and_of_implies_of_implies (H₁ : a ∧ b) (H₂ : a → c) (H₃ : b → d) : c ∧ d :=
and_implies H₂ H₃ H₁

theorem and_of_and_of_imp_left (H₁ : a ∧ c) (H : a → b) : b ∧ c :=
and_implies_left H H₁

theorem and_of_and_of_imp_right (H₁ : c ∧ a) (H : a → b) : c ∧ b :=
and_implies_right H H₁

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
or.elim H₁ (not_elim H₂) implies_self

theorem or_resolve_left (H₁ : a ∨ b) : ¬b → a :=
or_resolve_right (or.swap H₁)

theorem or.imp_distrib : ((a ∨ b) → c) ↔ ((a → c) ∧ (b → c)) :=
iff.intro
  (λH, and.intro (implies_trans or.inl H) (implies_trans or.inr H))
  (and.rec or.rec)

theorem or_iff_right_of_imp {a b : Prop} (Ha : a → b) : (a ∨ b) ↔ b :=
iff.intro (or.rec Ha implies_self) or.inr

theorem or_iff_left_of_imp {a b : Prop} (Hb : b → a) : (a ∨ b) ↔ a :=
iff.intro (or.rec implies_self Hb) or.inl

theorem or_iff_or (H1 : a ↔ c) (H2 : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
iff.intro (or.imp (iff.mp H1) (iff.mp H2)) (or.imp (iff.mpr H1) (iff.mpr H2))

/- distributivity -/

theorem and_distrib (a b c : Prop) : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
iff.intro
  (and.rec (λH, or.imp (and.intro H) (and.intro H)))
  (or.rec (and_implies_right or.inl) (and_implies_right or.inr))

theorem and_distrib_right (a b c : Prop) : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) :=
iff.trans (iff.trans and.comm (and_distrib c a b)) (or_iff_or and.comm and.comm)

theorem or_distrib (a b c : Prop) : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
iff.intro
  (or.rec (λH, and.intro (or.inl H) (or.inl H)) (and_implies or.inr or.inr))
  (and.rec (or.rec (implies_trans or.inl implies_intro) (implies_trans and.intro or.imp_right)))

theorem or_distrib_right (a b c : Prop) : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
iff.trans (iff.trans or.comm (or_distrib c a b)) (and_congr or.comm or.comm)

/- iff -/

definition iff_def : (a ↔ b) = ((a → b) ∧ (b → a)) := rfl

theorem forall_imp_forall {A : Type} {P Q : A → Prop} (H : ∀a, (P a → Q a)) (p : ∀a, P a) (a : A)
  : Q a :=
(H a) (p a)

theorem implies_iff {P : Prop} (Q : Prop) (p : P) : (P → Q) ↔ Q :=
iff.intro (λf, f p) implies_intro

end propositional


/- quantifiers -/

theorem exists_implies_distrib {A : Type} {b : Prop} {p : A → Prop} :
  ((∃ a : A, p a) → b) ↔ (∀ a : A, p a → b) :=
iff.intro (λ e x h, e ⟨x, h⟩) Exists.rec

theorem not_exists_iff_forall_not {A : Type} {p : A → Prop} :
  (¬ ∃ a : A, p a) ↔ ∀ a : A, ¬ p a :=
exists_implies_distrib


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

  lemma not_bexists_iff {A : Type} {s : set A} {p : A → Prop} :
    (¬ (∃ x ∈ s, p x)) ↔ (∀ x ∈ s, ¬ p x) :=
  begin
    rewrite not_exists_iff_forall_not,
    apply forall_congr,
    intro x,
    apply iff.intro,
    {  intros h1 xs px,
       exact h1 ⟨xs, px⟩ },
    intros h1 h2,
    cases h2 with xs px,
    exact h1 xs px
  end

/-
  lemma not_bforall_iff {A : Type} {s : set A} {p : A → Prop} :
    (¬ (∀ x ∈ s, p x)) ↔ (∃ x ∈ s, ¬ p x) :=
  calc (¬ (∀ x ∈ s, p x)) = ¬ ¬ (∃ x ∈ s, ¬ p x) :
    begin
      rewrite not_bounded_exists,
      apply (congr_arg not),
      apply bounded_forall_congr,
      intros x H,
      rewrite not_not_iff
    end
    ... = (∃ x ∈ s, ¬ p x) : by (rewrite not_not_iff)
-/

end
