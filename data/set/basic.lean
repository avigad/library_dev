/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors Jeremy Avigad, Leonardo de Moura

-- TODO: subset should have a weak implicit argument
-- TODO: in emacs mode, change "\sub" to regular subset, use "\ssub" for strict,
         similarly for "\sup"
-- TODO: and.comm and and.assoc should not have implicit arguments

-- QUESTION: could we somehow make the first argument in ∀ x ∈ a, ... implicit?
-/
import ...logic.basic
open function tactic

universe variables u v
variable {A : Type u}


/- definitions -/

namespace set

def strict_subset (a b : set A) := a ⊆ b ∧ a ≠ b

instance : has_ssubset (set A) := ⟨strict_subset⟩

end set


/- properties -/

namespace set

theorem ext {a b : set A} (h : ∀x, x ∈ a ↔ x ∈ b) : a = b :=
funext (take x, propext (h x))

theorem subset_refl (a : set A) : a ⊆ a := take x, assume h, h

theorem subset_trans {a b c : set A} (subab : a ⊆ b) (subbc : b ⊆ c) : a ⊆ c :=
take x, assume ax, subbc (subab ax)

theorem subset_antisymm {a b : set A} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
ext (λ x, iff.intro (λ ina, h₁ ina) (λ inb, h₂ inb))

-- an alterantive name
theorem eq_of_subset_of_subset {a b : set A} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
subset_antisymm @h₁ @h₂

theorem mem_of_subset_of_mem {s₁ s₂ : set A} {a : A} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
assume h₁ h₂, h₁ h₂

theorem strict_subset_irrefl (a : set A) : ¬ a ⊂ a :=
assume h, absurd rfl (and.elim_right h)


/- empty set -/

-- TODO: needs annotation
theorem not_mem_empty (x : A) : x ∉ (∅ : set A) :=
assume h, h

theorem mem_empty_eq (x : A) : (x ∈ (∅ : set A)) = false :=
rfl

theorem eq_empty_of_forall_not_mem {s : set A} (H : ∀ x, x ∉ s) : s = ∅ :=
ext (take x, iff.intro
  (assume xs, absurd xs (H x))
  (assume xe, absurd xe (not_mem_empty _)))

theorem ne_empty_of_mem {s : set A} {x : A} (h : x ∈ s) : s ≠ ∅ :=
begin intro hs, rewrite hs at h, apply not_mem_empty _ h end

-- classical!
theorem exists_mem_of_ne_empty {s : set A} (H : s ≠ ∅) : ∃ x, x ∈ s :=
sorry

theorem empty_subset (s : set A) : ∅ ⊆ s :=
take x, assume h, false_elim h

theorem eq_empty_of_subset_empty {s : set A} (H : s ⊆ ∅) : s = ∅ :=
subset_antisymm @H (@empty_subset _ s)

theorem subset_empty_iff (s : set A) : s ⊆ ∅ ↔ s = ∅ :=
sorry
-- iff.intro eq_empty_of_subset_empty (take xeq, by rewrite xeq; apply subset.refl ∅)

lemma bounded_forall_empty_iff {p : A → Prop} :
  (∀ x ∈ ∅, p x) ↔ true :=
iff.intro (take H, true.intro) (take H x H1, absurd H1 (not_mem_empty _))

/- universal set -/

definition univ : set A := λx, true

-- TODO: interesting -- fails if A is not specified
theorem mem_univ (x : A) : x ∈ @univ A :=
by triv

theorem mem_univ_iff (x : A) : x ∈ @univ A ↔ true := iff.rfl

theorem mem_univ_eq (x : A) : x ∈ @univ A = true := rfl

theorem empty_ne_univ [h : inhabited A] : (∅ : set A) ≠ univ :=
assume H : ∅ = univ,
absurd (mem_univ (inhabited.default A)) (eq.rec_on H (not_mem_empty _))

theorem subset_univ (s : set A) : s ⊆ univ := λ x H, trivial

theorem eq_univ_of_univ_subset {s : set A} (H : univ ⊆ s) : s = univ :=
eq_of_subset_of_subset (@subset_univ _ s) @H

theorem eq_univ_of_forall {s : set A} (H : ∀ x, x ∈ s) : s = univ :=
ext (take x, iff.intro (assume H', trivial) (assume H', H x))

/- union -/

theorem mem_union_left {x : A} {a : set A} (b : set A) : x ∈ a → x ∈ a ∪ b :=
assume h, or.inl h

theorem mem_union_right {x : A} {b : set A} (a : set A) : x ∈ b → x ∈ a ∪ b :=
assume h, or.inr h

theorem mem_unionl {x : A} {a b : set A} : x ∈ a → x ∈ a ∪ b :=
assume h, or.inl h

theorem mem_unionr {x : A} {a b : set A} : x ∈ b → x ∈ a ∪ b :=
assume h, or.inr h

theorem mem_or_mem_of_mem_union {x : A} {a b : set A} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b := H

theorem mem_union.elim {x : A} {a b : set A} {P : Prop}
    (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
or.elim H₁ H₂ H₃

theorem mem_union_iff (x : A) (a b : set A) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := iff.rfl

theorem mem_union_eq (x : A) (a b : set A) : x ∈ a ∪ b = (x ∈ a ∨ x ∈ b) := rfl

theorem union_self (a : set A) : a ∪ a = a :=
ext (take x, or_self _)

theorem union_empty (a : set A) : a ∪ ∅ = a :=
ext (take x, or_false _)

theorem empty_union (a : set A) : ∅ ∪ a = a :=
ext (take x, false_or _)

theorem union_comm (a b : set A) : a ∪ b = b ∪ a :=
ext (take x, or.comm)

theorem union_assoc (a b c : set A) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
ext (take x, or.assoc)

theorem union_left_comm (s₁ s₂ s₃ : set A) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
sorry
--left_comm union_comm union_assoc s₁ s₂ s₃

theorem union_right_comm (s₁ s₂ s₃ : set A) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
sorry
-- !right_comm union_comm union_assoc s₁ s₂ s₃

theorem subset_union_left (s t : set A) : s ⊆ s ∪ t := λ x H, or.inl H

theorem subset_union_right (s t : set A) : t ⊆ s ∪ t := λ x H, or.inr H

theorem union_subset {s t r : set A} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
λ x xst, or.elim xst (λ xs, sr xs) (λ xt, tr xt)

/- intersection -/

theorem mem_inter_iff (x : A) (a b : set A) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := iff.rfl

theorem mem_inter_eq (x : A) (a b : set A) : x ∈ a ∩ b = (x ∈ a ∧ x ∈ b) := rfl

theorem mem_inter {x : A} {a b : set A} (Ha : x ∈ a) (Hb : x ∈ b) : x ∈ a ∩ b :=
and.intro Ha Hb

theorem mem_of_mem_inter_left {x : A} {a b : set A} (H : x ∈ a ∩ b) : x ∈ a :=
and.left H

theorem mem_of_mem_inter_right {x : A} {a b : set A} (H : x ∈ a ∩ b) : x ∈ b :=
and.right H

theorem inter_self (a : set A) : a ∩ a = a :=
ext (take x, and_self _)

theorem inter_empty (a : set A) : a ∩ ∅ = ∅ :=
ext (take x, and_false _)

theorem empty_inter (a : set A) : ∅ ∩ a = ∅ :=
ext (take x, false_and _)

-- TODO: try this with the simplifier
theorem nonempty_of_inter_nonempty_right {T : Type} {s t : set T} (H : s ∩ t ≠ ∅) : t ≠ ∅ :=
suppose t = ∅,
have s ∩ t = ∅, from eq.subst (eq.symm this) (inter_empty s),
H this

theorem nonempty_of_inter_nonempty_left {T : Type} {s t : set T} (H : s ∩ t ≠ ∅) : s ≠ ∅ :=
suppose s = ∅,
have s ∩ t = ∅, from sorry, -- by rewrite this; apply empty_inter,
H this

-- TODO: and.comm should not have its argumetns implicit
theorem inter_comm (a b : set A) : a ∩ b = b ∩ a :=
ext (take x, and.comm)

-- TODO: same for and.assoc
theorem inter_assoc (a b c : set A) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
ext (take x, and.assoc)

theorem inter_left_comm (s₁ s₂ s₃ : set A) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
sorry
--!left_comm inter_comm inter_assoc s₁ s₂ s₃

theorem inter_right_comm (s₁ s₂ s₃ : set A) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
sorry
--!right_comm inter_comm inter_assoc s₁ s₂ s₃

theorem inter_univ (a : set A) : a ∩ univ = a :=
ext (take x, and_true _)

theorem univ_inter (a : set A) : univ ∩ a = a :=
ext (take x, true_and _)

theorem inter_subset_left (s t : set A) : s ∩ t ⊆ s := λ x H, and.left H

theorem inter_subset_right (s t : set A) : s ∩ t ⊆ t := λ x H, and.right H

theorem inter_subset_inter_right {s t : set A} (u : set A) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
take x, assume xsu, and.intro (H (and.left xsu)) (and.right xsu)

theorem inter_subset_inter_left {s t : set A} (u : set A) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
take x, assume xus, and.intro (and.left xus) (H (and.right xus))

theorem subset_inter {s t r : set A} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
λ x xr, and.intro (rs xr) (rt xr)

theorem not_mem_of_mem_of_not_mem_inter_left {s t : set A} {x : A} (Hxs : x ∈ s) (Hnm : x ∉ s ∩ t) : x ∉ t :=
  suppose x ∈ t,
  have x ∈ s ∩ t, from and.intro Hxs this,
  show false, from Hnm this

theorem not_mem_of_mem_of_not_mem_inter_right {s t : set A} {x : A} (Hxs : x ∈ t) (Hnm : x ∉ s ∩ t) : x ∉ s :=
  suppose x ∈ s,
  have x ∈ s ∩ t, from and.intro this Hxs,
  show false, from Hnm this

/- distributivity laws -/

theorem inter_distrib_left (s t u : set A) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
ext (take x, and_distrib _ _ _)

theorem inter_distrib_right (s t u : set A) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext (take x, and_distrib_right _ _ _)

theorem union_distrib_left (s t u : set A) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext (take x, or_distrib _ _ _)

theorem union_distrib_right (s t u : set A) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
ext (take x, or_distrib_right _ _ _)

/- set-builder notation -/

theorem subset_insert (x : A) (a : set A) : a ⊆ insert x a :=
take y, assume ys, or.inr ys

theorem mem_insert (x : A) (s : set A) : x ∈ insert x s :=
or.inl rfl

theorem mem_insert_of_mem {x : A} {s : set A} (y : A) : x ∈ s → x ∈ insert y s :=
assume h, or.inr h

theorem eq_or_mem_of_mem_insert {x a : A} {s : set A} : x ∈ insert a s → x = a ∨ x ∈ s :=
assume h, h

theorem mem_of_mem_insert_of_ne {x a : A} {s : set A} (xin : x ∈ insert a s) : x ≠ a → x ∈ s :=
or_resolve_right (eq_or_mem_of_mem_insert xin)

-- TODO: is it possible to mark eq.substr as a recursor so that it can be used in the next
--       two of examples?

section
variables (a b : A) (p : A → Prop)

example (H : b = a) (H' : p a) : p b :=
eq.subst (eq.symm H) H'

example (H : b = a) (H' : p a) : p b :=
eq.substr H H'
end

theorem mem_insert_eq (x a : A) (s : set A) : x ∈ insert a s = (x = a ∨ x ∈ s) :=
propext (iff.intro eq_or_mem_of_mem_insert
  (λ H, or.elim H
    (λ H', (eq.subst (eq.symm H') (mem_insert a s)))
    (λ H', mem_insert_of_mem _ H')))

theorem insert_eq_of_mem {a : A} {s : set A} (H : a ∈ s) : insert a s = s :=
ext (λ x, eq.subst (eq.symm (mem_insert_eq x a s))
  (or_iff_right_of_imp (λ H1, eq.subst (eq.symm H1) H)))


--   (or_iff_right_of_imp (λH1, eq.substr H1 H)))

theorem insert.comm (x y : A) (s : set A) : insert x (insert y s) = insert y (insert x s) :=
sorry
-- ext (take a, by rewrite [*mem_insert_eq, propext !or.left_comm])

-- useful in proofs by induction
theorem forall_of_forall_insert {P : A → Prop} {a : A} {s : set A}
    (H : ∀ x, x ∈ insert a s → P x) :
  ∀ x, x ∈ s → P x :=
λ x xs, H x (mem_insert_of_mem _ xs)

lemma bounded_forall_insert_iff {P : A → Prop} {a : A} {s : set A} :
  (∀ x ∈ insert a s, P x) ↔ P a ∧ (∀x ∈ s, P x) :=
sorry
/-
begin
  apply iff.intro, all_goals (intro H),
  { apply and.intro,
    { apply H, apply mem_insert },
    { intro x Hx, apply H, apply mem_insert_of_mem, assumption } },
  { intro x Hx, cases Hx with eq Hx,
    { cases eq, apply (and.elim_left H) },
    { apply (and.elim_right H), assumption } }
end
-/

/- singleton -/

theorem singleton_eq (a : A) : ({a} : set A) = insert a ∅ := rfl

-- TODO: interesting: the theorem fails to elaborate without the annotation
theorem mem_singleton_iff (a b : A) : a ∈ ({b} : set A) ↔ a = b :=
iff.intro
  (assume ainb,
    or.elim (ainb : a = b ∨ false) (λ aeqb, aeqb) (λ f, false.elim f))
  (assume aeqb, or.inl aeqb)

-- TODO: again, annotation needed
theorem mem_singleton (a : A) : a ∈ ({a} : set A) := mem_insert a _

theorem eq_of_mem_singleton {x y : A} (h : x ∈ ({y} : set A)) : x = y :=
or.elim (eq_or_mem_of_mem_insert h)
  (suppose x = y, this)
  (suppose x ∈ (∅ : set A), absurd this (not_mem_empty _))

theorem mem_singleton_of_eq {x y : A} (H : x = y) : x ∈ ({y} : set A) :=
eq.subst (eq.symm H) (mem_singleton y)

theorem insert_eq (x : A) (s : set A) : insert x s = ({x} : set A) ∪ s :=
ext (take y, iff.intro
  (suppose y ∈ insert x s,
    or.elim this (suppose y = x, or.inl (or.inl this)) (suppose y ∈ s, or.inr this))
  (suppose y ∈ ({x} : set A) ∪ s,
    or.elim this
      (suppose y ∈ ({x} : set A), or.inl (eq_of_mem_singleton this))
      (suppose y ∈ s, or.inr this)))

theorem pair_eq_singleton (a : A) : ({a, a} : set A) = {a} :=
sorry
-- by rewrite [insert_eq_of_mem !mem_singleton]

theorem singleton_ne_empty (a : A) : ({a} : set A) ≠ ∅ :=
sorry
/-
begin
  intro H,
  apply not_mem_empty a,
  rewrite -H,
  apply mem_insert
end
-/

/- separation -/

theorem mem_sep {s : set A} {P : A → Prop} {x : A} (xs : x ∈ s) (Px : P x) : x ∈ {x ∈ s | P x} :=
and.intro xs Px

theorem eq_sep_of_subset {s t : set A} (ssubt : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
ext (take x, iff.intro
  (suppose x ∈ s, and.intro (ssubt this) this)
  (suppose x ∈ {x ∈ t | x ∈ s}, and.right this))

theorem mem_sep_iff {s : set A} {P : A → Prop} {x : A} : x ∈ {x ∈ s | P x} ↔ x ∈ s ∧ P x :=
iff.rfl

theorem sep_subset (s : set A) (P : A → Prop) : {x ∈ s | P x} ⊆ s :=
take x, assume H, and.left H

theorem forall_not_of_sep_empty {s : set A} {P : A → Prop} (H : {x ∈ s | P x} = ∅) : ∀ x ∈ s, ¬ P x :=
  take x, suppose x ∈ s, suppose P x,
  have x ∈ {x ∈ s | P x}, from and.intro (by assumption) this,
  show false, from ne_empty_of_mem this H

/- complement -/

theorem mem_compl {s : set A} {x : A} (H : x ∉ s) : x ∈ -s := H

theorem not_mem_of_mem_compl {s : set A} {x : A} (H : x ∈ -s) : x ∉ s := H

theorem mem_compl_iff (s : set A) (x : A) : x ∈ -s ↔ x ∉ s := iff.rfl

theorem inter_compl_self (s : set A) : s ∩ -s = ∅ :=
sorry
-- ext (take x, and_not_self_iff _)

theorem compl_inter_self (s : set A) : -s ∩ s = ∅ :=
sorry
-- ext (take x, !not_and_self_iff)

/- some classical identities -/

section

  theorem compl_empty : -(∅ : set A) = univ :=
  ext (take x, iff.intro (assume H, trivial) (assume H, not_false))

  theorem compl_union (s t : set A) : -(s ∪ t) = -s ∩ -t :=
  sorry
--  ext (take x, !not_or_iff_not_and_not)

  theorem compl_compl (s : set A) : -(-s) = s :=
  sorry
--  ext (take x, !not_not_iff)

  theorem compl_inter (s t : set A) : -(s ∩ t) = -s ∪ -t :=
  sorry
--  ext (take x, !not_and_iff_not_or_not)

  theorem compl_univ : -(univ : set A) = ∅ :=
  sorry
--  by rewrite [-compl_empty, compl_compl]

  theorem union_eq_compl_compl_inter_compl (s t : set A) : s ∪ t = -(-s ∩ -t) :=
  sorry
--  ext (take x, !or_iff_not_and_not)

  theorem inter_eq_compl_compl_union_compl (s t : set A) : s ∩ t = -(-s ∪ -t) :=
  sorry
--  ext (take x, !and_iff_not_or_not)

  theorem union_compl_self (s : set A) : s ∪ -s = univ :=
  sorry
--  ext (take x, !or_not_self_iff)

  theorem compl_union_self (s : set A) : -s ∪ s = univ :=
  sorry
--  ext (take x, !not_or_self_iff)

  theorem compl_comp_compl : compl ∘ compl = @id (set A) :=
  funext (λ s, compl_compl s)
end

/- set difference -/

theorem mem_diff {s t : set A} {x : A} (H1 : x ∈ s) (H2 : x ∉ t) : x ∈ s \ t :=
and.intro H1 H2

theorem mem_of_mem_diff {s t : set A} {x : A} (H : x ∈ s \ t) : x ∈ s :=
and.left H

theorem not_mem_of_mem_diff {s t : set A} {x : A} (H : x ∈ s \ t) : x ∉ t :=
and.right H

theorem mem_diff_iff (s t : set A) (x : A) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := iff.rfl

theorem mem_diff_eq (s t : set A) (x : A) : x ∈ s \ t = (x ∈ s ∧ x ∉ t) := rfl

theorem diff_eq (s t : set A) : s \ t = s ∩ -t := rfl

theorem union_diff_cancel {s t : set A} [dec : Π x, decidable (x ∈ s)] (H : s ⊆ t) : s ∪ (t \ s) = t :=
ext (take x, iff.intro
  (assume H1 : x ∈ s ∪ (t \ s), or.elim H1 (assume H2, H H2) (assume H2, and.left H2))
  (assume H1 : x ∈ t,
    decidable.by_cases
      (suppose x ∈ s, or.inl this)
      (suppose x ∉ s, or.inr (and.intro H1 this))))

theorem diff_subset (s t : set A) : s \ t ⊆ s := @inter_subset_left _ s _

theorem compl_eq_univ_diff (s : set A) : -s = univ \ s :=
ext (take x, iff.intro (assume H, and.intro trivial H) (assume H, and.right H))

/- powerset -/

theorem mem_powerset {x s : set A} (H : x ⊆ s) : x ∈ 𝒫 s := @H

theorem subset_of_mem_powerset {x s : set A} (H : x ∈ 𝒫 s) : x ⊆ s := @H

theorem mem_powerset_iff (x s : set A) : x ∈ 𝒫 s ↔ x ⊆ s := iff.rfl

/- function image -/

section image

variables {B C : Type}

-- TODO: "abbreviation" is gone?
@[reducible] def eq_on (f1 f2 : A → B) (a : set A) : Prop :=
∀ x ∈ a, f1 x = f2 x

-- TODO: what notation to use for image?
infix ` '~ `:80 := image

-- QUESTION: I guess we can't use H3.1 for and.left H3?
theorem image_eq_image_of_eq_on {f1 f2 : A → B} {a : set A} (H1 : eq_on f1 f2 a) :
  f1 '~ a = f2 '~ a :=
ext (take y, iff.intro
  (assume ⟨x, (H3 : x ∈ a ∧ f1 x = y)⟩,
    have H4 : x ∈ a, from and.left H3,
    have H5 : f2 x = y, from eq.trans (eq.symm (H1 _ H4)) (and.right H3),
    ⟨x, H4, H5⟩)
  (assume ⟨x, (H3 : x ∈ a ∧ f2 x = y)⟩,
    have H4 : x ∈ a, from and.left H3,
    have H5 : f1 x = y, from eq.trans (H1 _ H4) (and.right H3),
    ⟨x, H4, H5⟩))

/-
ext (take y, iff.intro
  (assume H2,
    match H2 with
    | ⟨x, (H3 : x ∈ a ∧ f1 x = y)⟩ :=
      have H4 : x ∈ a, from and.left H3,
      have H5 : f2 x = y, from eq.trans (eq.symm (H1 _ H4)) (and.right H3),
      exists.intro x (and.intro H4 H5)
    end)
  (assume H2,
    match H2 with
    | ⟨x, (H3 : x ∈ a ∧ f2 x = y)⟩ :=
      have H4 : x ∈ a, from and.left H3,
      have H5 : f1 x = y, from eq.trans (H1 _ H4) (and.right H3),
      exists.intro x (and.intro H4 H5)
    end))
-/

theorem mem_image {f : A → B} {a : set A} {x : A} {y : B}
  (H1 : x ∈ a) (H2 : f x = y) : y ∈ f '~ a :=
exists.intro x (and.intro H1 H2)

theorem mem_image_of_mem (f : A → B) {x : A} {a : set A} (H : x ∈ a) : f x ∈ image f a :=
mem_image H rfl

-- TODO: this nested pattern match in the assume is impressive!
lemma image_comp (f : B → C) (g : A → B) (a : set A) : (f ∘ g) '~ a = f '~ (g '~ a) :=
ext (take z,
  iff.intro
    (assume ⟨x, (Hx₁ : x ∈ a), (Hx₂ : f (g x) = z)⟩,
      have g x ∈ g '~ a,
        from mem_image Hx₁ rfl,
      show z ∈ f '~ (g '~ a),
        from mem_image this Hx₂)
    (assume ⟨y, ⟨x, (Hz₁ : x ∈ a), (Hz₂ : g x = y)⟩, (Hy₂ : f y = z)⟩,
      have f (g x) = z,
        from eq.subst (eq.symm Hz₂) Hy₂,
      show z ∈ (f ∘ g) '~ a,
        from mem_image Hz₁ this))

/- the old proof
ext (take z,
  iff.intro
    (assume Hz : z ∈ (f ∘ g) '~ a,
      obtain x (Hx₁ : x ∈ a) (Hx₂ : f (g x) = z), from Hz,
      have Hgx : g x ∈ g '~ a, from mem_image Hx₁ rfl,
      show z ∈ f '~ (g '~ a), from mem_image Hgx Hx₂)
    (assume Hz : z ∈ f '~ (g 'a),
      obtain y (Hy₁ : y ∈ g '~ a) (Hy₂ : f y = z), from Hz,
      obtain x (Hz₁ : x ∈ a) (Hz₂ : g x = y),      from Hy₁,
      show z ∈ (f ∘ g) '~ a, from mem_image Hz₁ (Hz₂⁻¹ ▸ Hy₂)))
-/

lemma image_subset {a b : set A} (f : A → B) (H : a ⊆ b) : f '~ a ⊆ f '~ b :=
take y,
assume ⟨x, Hx₁, Hx₂⟩,
mem_image (H Hx₁) Hx₂

/- the old proof
take y, assume Hy : y ∈ f '~ a,
obtain x (Hx₁ : x ∈ a) (Hx₂ : f x = y), from Hy,
mem_image (H Hx₁) Hx₂
-/

/- stopped here. -/









/-
theorem image_union (f : A → B) (s t : set A) :
  image f (s ∪ t) = image f s ∪ image f t :=
ext (take y, iff.intro
  (assume H : y ∈ image f (s ∪ t),
    obtain x [(xst : x ∈ s ∪ t) (fxy : f x = y)], from H,
    or.elim xst
      (assume xs, or.inl (mem_image xs fxy))
      (assume xt, or.inr (mem_image xt fxy)))
  (assume H : y ∈ image f s ∪ image f t,
    or.elim H
      (assume yifs : y ∈ image f s,
        obtain x [(xs : x ∈ s) (fxy : f x = y)], from yifs,
        mem_image (or.inl xs) fxy)
      (assume yift : y ∈ image f t,
        obtain x [(xt : x ∈ t) (fxy : f x = y)], from yift,
        mem_image (or.inr xt) fxy)))

theorem image_empty (f : A → B) : image f ∅ = ∅ :=
eq_empty_of_forall_not_mem
  (take y, suppose y ∈ image f ∅,
    obtain x [(H : x ∈ empty) H'], from this,
    H)

theorem mem_image_compl (t : set A) (S : set (set A)) :
  t ∈ compl '~ S ↔ -t ∈ S :=
iff.intro
  (suppose t ∈ compl '~ S,
    obtain t' [(Ht' : t' ∈ S) (Ht : -t' = t)], from this,
    show -t ∈ S, by rewrite [-Ht, compl_compl]; exact Ht')
  (suppose -t ∈ S,
    have -(-t) ∈ compl 'S, from mem_image_of_mem compl this,
    show t ∈ compl 'S, from compl_compl t ▸ this)


theorem image_id (s : set A) : id '~ s = s :=
ext (take x, iff.intro
  (suppose x ∈ id '~ s,
    obtain x' [(Hx' : x' ∈ s) (x'eq : x' = x)], from this,
    show x ∈ s, by rewrite [-x'eq]; apply Hx')
  (suppose x ∈ s, mem_image_of_mem id this))

theorem compl_compl_image (S : set (set A)) :
  compl '~ (compl '~ S) = S :=
by rewrite [-image_comp, compl_comp_compl, image_id]

lemma bounded_forall_image_of_bounded_forall {f : A → B} {S : set A} {P : B → Prop}
  (H : ∀ x ∈ S, P (f x)) : ∀ y ∈ f '~ S, P y :=
begin
  intro x' Hx;
  cases Hx with x Hx;
  cases Hx with Hx eq;
  rewrite (eq⁻¹);
  apply H;
  assumption
end

lemma bounded_forall_image_iff {f : A → B} {S : set A} {P : B → Prop} :
  (∀ y ∈ f '~ S, P y) ↔ (∀ x ∈ S, P (f x)) :=
iff.intro (take H x Hx, H _ (!mem_image_of_mem `x ∈ S`)) bounded_forall_image_of_bounded_forall

lemma image_insert_eq {f : A → B} {a : A} {S : set A} :
  f '~ insert a S = insert (f a) (f '~ S) :=
begin
  apply set.ext,
  intro x, apply iff.intro, all_goals (intros H),
  { cases H with y Hy, cases Hy with Hy eq, rewrite (eq⁻¹), cases Hy with y_eq,
    { rewrite y_eq, apply mem_insert },
    { apply mem_insert_of_mem, apply mem_image_of_mem, assumption } },
  { cases H with eq Hx,
    { rewrite eq, apply mem_image_of_mem, apply mem_insert },
    { cases Hx with y Hy, cases Hy with Hy eq,
      rewrite (eq⁻¹), apply mem_image_of_mem, apply mem_insert_of_mem, assumption } }
end
-/

end image

/-
/- collections of disjoint sets -/

definition disjoint_sets (S : set (set A)) : Prop := ∀ a b, a ∈ S → b ∈ S → a ≠ b → a ∩ b = ∅

theorem disjoint_sets_empty : disjoint_sets (∅ : set (set A)) :=
take a b, assume H, !not.elim !not_mem_empty H

theorem disjoint_sets_union {s t : set (set A)} (Hs : disjoint_sets s) (Ht : disjoint_sets t)
    (H : ∀ x y, x ∈ s ∧ y ∈ t → x ∩ y = ∅) :
  disjoint_sets (s ∪ t) :=
take a b, assume Ha Hb Hneq, or.elim Ha
 (assume H1, or.elim Hb
   (suppose b ∈ s, (Hs a b) H1 this Hneq)
   (suppose b ∈ t, (H a b) (and.intro H1 this)))
 (assume H2, or.elim Hb
   (suppose b ∈ s, !inter_comm ▸ ((H b a) (and.intro this H2)))
   (suppose b ∈ t, (Ht a b) H2 this Hneq))

theorem disjoint_sets_singleton (s : set (set A)) : disjoint_sets {s} :=
take a b, assume Ha Hb  Hneq,
absurd (eq.trans ((iff.elim_left !mem_singleton_iff) Ha) ((iff.elim_left !mem_singleton_iff) Hb)⁻¹)
    Hneq

/- large unions -/

section large_unions
  variables {I : Type}
  variable a : set I
  variable b : I → set A
  variable C : set (set A)

  definition sUnion : set A := {x : A | ∃ c ∈ C, x ∈ c}
  definition sInter : set A := {x : A | ∀ c ∈ C, x ∈ c}

  prefix `⋃₀`:110 := sUnion
  prefix `⋂₀`:110 := sInter

  definition Union  : set A := {x : A | ∃i, x ∈ b i}
  definition Inter  : set A := {x : A | ∀i, x ∈ b i}

  notation `⋃` binders `, ` r:(scoped f, Union f) := r
  notation `⋂` binders `, ` r:(scoped f, Inter f) := r

  definition bUnion : set A := {x : A | ∃ i ∈ a, x ∈ b i}
  definition bInter : set A := {x : A | ∀ i ∈ a, x ∈ b i}

  notation `⋃` binders ` ∈ ` s `, ` r:(scoped f, bUnion s f) := r
  notation `⋂` binders ` ∈ ` s `, ` r:(scoped f, bInter s f) := r

end large_unions

-- sUnion and sInter: a collection (set) of sets

theorem mem_sUnion {x : A} {t : set A} {S : set (set A)} (Hx : x ∈ t) (Ht : t ∈ S) :
  x ∈ ⋃₀ S :=
exists.intro t (and.intro Ht Hx)

theorem not_mem_of_not_mem_sUnion {x : A} {t : set A} {S : set (set A)} (Hx : x ∉ ⋃₀ S) (Ht : t ∈ S) :
        x ∉ t :=
  suppose x ∈ t,
  have x ∈ ⋃₀ S, from mem_sUnion this Ht,
  show false, from Hx this

theorem mem_sInter {x : A} {t : set A} {S : set (set A)} (H : ∀ t ∈ S, x ∈ t) :
  x ∈ ⋂₀ S :=
H

theorem sInter_subset_of_mem {S : set (set A)} {t : set A} (tS : t ∈ S) :
  (⋂₀ S) ⊆ t :=
take x, assume H, H t tS

theorem subset_sUnion_of_mem {S : set (set A)} {t : set A} (tS : t ∈ S) :
  t ⊆ (⋃₀ S) :=
take x, assume H, exists.intro t (and.intro tS H)

theorem sUnion_empty : ⋃₀ ∅ = (∅ : set A) :=
eq_empty_of_forall_not_mem
  (take x, suppose x ∈ sUnion ∅,
    obtain t [(Ht : t ∈ ∅) Ht'], from this,
    show false, from Ht)

theorem sInter_empty : ⋂₀ ∅ = (univ : set A) :=
eq_univ_of_forall (λ x s H, false.elim H)

theorem sUnion_singleton (s : set A) : ⋃₀ {s} = s :=
ext (take x, iff.intro
  (suppose x ∈ sUnion {s},
    obtain u [(Hu : u ∈ {s}) (xu : x ∈ u)], from this,
    have u = s, from eq_of_mem_singleton Hu,
    show x ∈ s, by rewrite -this; apply xu)
  (suppose x ∈ s,
    mem_sUnion this (mem_singleton s)))

theorem sInter_singleton (s : set A) : ⋂₀ {s} = s :=
ext (take x, iff.intro
  (suppose x ∈ ⋂₀ {s}, show x ∈ s, from this (mem_singleton s))
  (suppose x ∈ s, take u, suppose u ∈ {s},
    show x ∈ u, by rewrite [eq_of_mem_singleton this]; assumption))

theorem sUnion_union (S T : set (set A)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T :=
ext (take x, iff.intro
  (suppose x ∈ sUnion (S ∪ T),
    obtain u [(Hu : u ∈ S ∪ T) (xu : x ∈ u)], from this,
    or.elim Hu
      (assume uS, or.inl (mem_sUnion xu uS))
      (assume uT, or.inr (mem_sUnion xu uT)))
  (suppose x ∈ sUnion S ∪ sUnion T,
    or.elim this
      (suppose x ∈ sUnion S,
        obtain u [(uS : u ∈ S) (xu : x ∈ u)], from this,
        mem_sUnion xu (or.inl uS))
      (suppose x ∈ sUnion T,
        obtain u [(uT : u ∈ T) (xu : x ∈ u)], from this,
        mem_sUnion xu (or.inr uT))))

theorem sInter_union (S T : set (set A)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
ext (take x, iff.intro
  (assume H : x ∈ ⋂₀ (S ∪ T),
    and.intro (λ u uS, H (or.inl uS)) (λ u uT, H (or.inr uT)))
  (assume H : x ∈ ⋂₀ S ∩ ⋂₀ T,
    take u, suppose u ∈ S ∪ T, or.elim this (λ uS, and.left H u uS) (λ uT, and.right H u uT)))

theorem sUnion_insert (s : set A) (T : set (set A)) :
  ⋃₀ (insert s T) = s ∪ ⋃₀ T :=
by rewrite [insert_eq, sUnion_union, sUnion_singleton]

theorem sInter_insert (s : set A) (T : set (set A)) :
  ⋂₀ (insert s T) = s ∩ ⋂₀ T :=
by rewrite [insert_eq, sInter_union, sInter_singleton]

theorem compl_sUnion (S : set (set A)) :
  - ⋃₀ S = ⋂₀ (compl '~ S) :=
ext (take x, iff.intro
  (assume H : x ∈ -(⋃₀ S),
    take t, suppose t ∈ compl '~ S,
    obtain t' [(Ht' : t' ∈ S) (Ht : -t' = t)], from this,
    have x ∈ -t', from suppose x ∈ t', H (mem_sUnion this Ht'),
    show x ∈ t, by rewrite -Ht; apply this)
  (assume H : x ∈ ⋂₀ (compl '~ S),
    suppose x ∈ ⋃₀ S,
    obtain t [(tS : t ∈ S) (xt : x ∈ t)], from this,
    have -t ∈ compl '~ S, from mem_image_of_mem compl tS,
    have x ∈ -t, from H this,
    show false, proof this xt qed))

theorem sUnion_eq_compl_sInter_compl (S : set (set A)) :
  ⋃₀ S = - ⋂₀ (compl '~ S) :=
by rewrite [-compl_compl, compl_sUnion]

theorem compl_sInter (S : set (set A)) :
  - ⋂₀ S = ⋃₀ (compl '~ S) :=
by rewrite [sUnion_eq_compl_sInter_compl, compl_compl_image]

theorem sInter_eq_comp_sUnion_compl (S : set (set A)) :
   ⋂₀ S = -(⋃₀ (compl '~ S)) :=
by rewrite [-compl_compl, compl_sInter]

theorem inter_sUnion_nonempty_of_inter_nonempty {s t : set A} {S : set (set A)} (Hs : t ∈ S) (Hne : s ∩ t ≠ ∅) :
        s ∩ ⋃₀ S ≠ ∅ :=
  obtain x Hsx Htx, from exists_mem_of_ne_empty Hne,
  have x ∈ ⋃₀ S, from mem_sUnion Htx Hs,
  ne_empty_of_mem (mem_inter Hsx this)

theorem sUnion_inter_nonempty_of_inter_nonempty {s t : set A} {S : set (set A)} (Hs : t ∈ S) (Hne : t ∩ s ≠ ∅) :
        (⋃₀ S) ∩ s ≠ ∅ :=
  obtain x Htx Hsx, from exists_mem_of_ne_empty Hne,
  have x ∈ ⋃₀ S, from mem_sUnion Htx Hs,
  ne_empty_of_mem (mem_inter this Hsx)

-- Union and Inter: a family of sets indexed by a type

theorem Union_subset {I : Type} {b : I → set A} {c : set A} (H : ∀ i, b i ⊆ c) : (⋃ i, b i) ⊆ c :=
take x,
suppose x ∈ Union b,
obtain i (Hi : x ∈ b i), from this,
show x ∈ c, from H i Hi

theorem subset_Inter {I : Type} {b : I → set A} {c : set A} (H : ∀ i, c ⊆ b i) : c ⊆ ⋂ i, b i :=
λ x cx i, H i cx

theorem Union_eq_sUnion_image {A I : Type} (s : I → set A) : (⋃ i, s i) = ⋃₀ (s '~ univ) :=
ext (take x, iff.intro
  (suppose x ∈ Union s,
    obtain i (Hi : x ∈ s i), from this,
    mem_sUnion Hi (mem_image_of_mem s trivial))
  (suppose x ∈ sUnion (s '~ univ),
    obtain t [(Ht : t ∈ s '~ univ) (Hx : x ∈ t)], from this,
    obtain i [univi (Hi : s i = t)], from Ht,
    exists.intro i (show x ∈ s i, by rewrite Hi; apply Hx)))

theorem Inter_eq_sInter_image {A I : Type} (s : I → set A) : (⋂ i, s i) = ⋂₀ (s '~ univ) :=
ext (take x, iff.intro
  (assume H : x ∈ Inter s,
    take t,
    suppose t ∈ s 'univ,
    obtain i [univi (Hi : s i = t)], from this,
    show x ∈ t, by rewrite -Hi; exact H i)
  (assume H : x ∈ ⋂₀ (s '~ univ),
    take i,
    have s i ∈ s '~ univ, from mem_image_of_mem s trivial,
    show x ∈ s i, from H this))

theorem compl_Union {A I : Type} (s : I → set A) : - (⋃ i, s i) = (⋂ i, - s i) :=
by rewrite [Union_eq_sUnion_image, compl_sUnion, -image_comp, -Inter_eq_sInter_image]

theorem compl_Inter {A I : Type} (s : I → set A) : -(⋂ i, s i) = (⋃ i, - s i) :=
by rewrite [Inter_eq_sInter_image, compl_sInter, -image_comp, -Union_eq_sUnion_image]

theorem Union_eq_comp_Inter_comp {A I : Type} (s : I → set A) : (⋃ i, s i) = - (⋂ i, - s i) :=
by rewrite [-compl_compl, compl_Union]

theorem Inter_eq_comp_Union_comp {A I : Type} (s : I → set A) : (⋂ i, s i) = - (⋃ i, -s i) :=
by rewrite [-compl_compl, compl_Inter]

lemma inter_distrib_Union_left {A I : Type} (s : I → set A) (a : set A) :
  a ∩ (⋃ i, s i) = ⋃ i, a ∩ s i :=
ext (take x, iff.intro
  (assume H, obtain i Hi, from and.elim_right H,
    have x ∈ a ∩ s i, from and.intro (and.elim_left H) Hi,
    show _, from exists.intro i this)
  (assume H, obtain i [xa xsi], from H,
   show _, from and.intro xa (exists.intro i xsi)))

section
  local attribute classical.prop_decidable [instance]

  lemma union_distrib_Inter_left {A I : Type} (s : I → set A) (a : set A) :
    a ∪ (⋂ i, s i) = ⋂ i, a ∪ s i :=
  ext (take x, iff.intro
    (assume H, or.elim H
      (assume H1, take i, or.inl H1)
      (assume H1, take i, or.inr (H1 i)))
    (assume H,
      by_cases
        (suppose x ∈ a, or.inl this)
        (suppose x ∉ a, or.inr (take i, or.resolve_left (H i) this))))
end

-- these are useful for turning binary union / intersection into countable ones

definition bin_ext (s t : set A) (n : ℕ) : set A :=
nat.cases_on n s (λ m, t)

lemma Union_bin_ext (s t : set A) : (⋃ i, bin_ext s t i) = s ∪ t :=
ext (take x, iff.intro
  (assume H,
    obtain i (Hi : x ∈ (bin_ext s t) i), from H,
    by cases i; apply or.inl Hi; apply or.inr Hi)
  (assume H,
    or.elim H
      (suppose x ∈ s, exists.intro 0 this)
      (suppose x ∈ t, exists.intro 1 this)))

lemma Inter_bin_ext (s t : set A) : (⋂ i, bin_ext s t i) = s ∩ t :=
ext (take x, iff.intro
  (assume H, and.intro (H 0) (H 1))
  (assume H, by intro i; cases i;
    apply and.elim_left H; apply and.elim_right H))

-- bUnion and bInter: a family of sets indexed by a set ("b" is for bounded)

variable {B : Type}

theorem mem_bUnion {s : set A} {f : A → set B} {x : A} {y : B}
    (xs : x ∈ s) (yfx : y ∈ f x) :
  y ∈ ⋃ x ∈ s, f x :=
exists.intro x (and.intro xs yfx)

theorem mem_bInter {s : set A} {f : A → set B} {y : B} (H : ∀ x ∈ s, y ∈ f x) :
  y ∈ ⋂ x ∈ s, f x :=
H

theorem bUnion_subset {s : set A} {t : set B} {f : A → set B} (H : ∀ x ∈ s, f x ⊆ t) :
  (⋃ x ∈ s, f x) ⊆ t :=
take y, assume Hy,
obtain x [xs yfx], from Hy,
show y ∈ t, from H xs yfx

theorem subset_bInter {s : set A} {t : set B} {f : A → set B} (H : ∀ x ∈ s, t ⊆ f x) :
  t ⊆ ⋂ x ∈ s, f x :=
take y, assume yt, take x, assume xs, H xs yt

theorem subset_bUnion_of_mem {s : set A} {f : A → set B} {x : A} (xs : x ∈ s) :
  f x ⊆ ⋃ x ∈ s, f x :=
take y, assume Hy, mem_bUnion xs Hy

theorem bInter_subset_of_mem {s : set A} {f : A → set B} {x : A} (xs : x ∈ s) :
  (⋂ x ∈ s, f x) ⊆ f x :=
take y, assume Hy, Hy x xs

theorem bInter_empty (f : A → set B) : (⋂ x ∈ (∅ : set A), f x) = univ :=
eq_univ_of_forall (take y x xine, absurd xine !not_mem_empty)

theorem bInter_singleton (a : A) (f : A → set B) : (⋂ x ∈ {a}, f x) = f a :=
ext (take y, iff.intro
  (assume H, H a !mem_singleton)
  (assume H, λ x xa, by rewrite [eq_of_mem_singleton xa]; apply H))

theorem bInter_union (s t : set A) (f : A → set B) :
  (⋂ x ∈ s ∪ t, f x) = (⋂ x ∈ s, f x) ∩ (⋂ x ∈ t, f x) :=
ext (take y, iff.intro
  (assume H, and.intro (λ x xs, H x (or.inl xs)) (λ x xt, H x (or.inr xt)))
  (assume H, λ x xst, or.elim (xst) (λ xs, and.left H x xs) (λ xt, and.right H x xt)))

theorem bInter_insert (a : A) (s : set A) (f : A → set B) :
  (⋂ x ∈ insert a s, f x) = f a ∩ (⋂ x ∈ s, f x) :=
by rewrite [insert_eq, bInter_union, bInter_singleton]

theorem bInter_pair (a b : A) (f : A → set B) :
  (⋂ x ∈ {a, b}, f x) = f a ∩ f b :=
by rewrite [*bInter_insert, bInter_empty, inter_univ]

theorem bUnion_empty (f : A → set B) : (⋃ x ∈ (∅ : set A), f x) = ∅ :=
eq_empty_of_forall_not_mem (λ y H, obtain x [xine yfx], from H,
  !not_mem_empty xine)

theorem bUnion_singleton (a : A) (f : A → set B) : (⋃ x ∈ {a}, f x) = f a :=
ext (take y, iff.intro
  (assume H, obtain x [xina yfx], from H,
    show y ∈ f a, by rewrite [-eq_of_mem_singleton xina]; exact yfx)
  (assume H, exists.intro a (and.intro !mem_singleton H)))

theorem bUnion_union (s t : set A) (f : A → set B) :
  (⋃ x ∈ s ∪ t, f x) = (⋃ x ∈ s, f x) ∪ (⋃ x ∈ t, f x) :=
ext (take y, iff.intro
  (assume H, obtain x [xst yfx], from H,
    or.elim xst
      (λ xs, or.inl (exists.intro x (and.intro xs yfx)))
      (λ xt, or.inr (exists.intro x (and.intro xt yfx))))
  (assume H, or.elim H
    (assume H1, obtain x [xs yfx], from H1,
      exists.intro x (and.intro (or.inl xs) yfx))
    (assume H1, obtain x [xt yfx], from H1,
      exists.intro x (and.intro (or.inr xt) yfx))))

theorem bUnion_insert (a : A) (s : set A) (f : A → set B) :
  (⋃ x ∈ insert a s, f x) = f a ∪ (⋃ x ∈ s, f x) :=
by rewrite [insert_eq, bUnion_union, bUnion_singleton]

theorem bUnion_pair (a b : A) (f : A → set B) :
  (⋃ x ∈ {a, b}, f x) = f a ∪ f b :=
by rewrite [*bUnion_insert, bUnion_empty, union_empty]
-/

end set
