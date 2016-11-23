/-
  TODO: better or alternative names for theorems in init.core.
-/

def and_intro {a b : Prop} (ha : a) (hb : b) : and a b := and.intro ha hb

-- keep both
def and_left := @and.elim_left

-- keep both
def and_right := @and.elim_right

def or_inl {a b : Prop} (ha : a) : or a b := or.inl ha

def or_inr {a b : Prop} (hb : b) : or a b := or.inr hb

def or_intro_left {a : Prop} (b : Prop) (ha : a) : or a b := or.inl ha

def or_intro_right (a : Prop) {b : Prop} (hb : b) : or a b := or.inr hb

section
  universe variable u
  variables {A : Type u}
  variables {a b c a': A}

  theorem eq_refl {A : Type u} (a : A) : a = a := eq.refl a

  attribute [elab_as_eliminator]
  theorem eq_subst {P : A → Prop} (H₁ : a = b) (H₂ : P a) : P b := eq.rec H₂ H₁

  theorem eq_trans (H₁ : a = b) (H₂ : b = c) : a = c := eq_subst H₂ H₁

  theorem eq_symm : a = b → b = a := λ h, eq.rec (eq_refl a) h
end

/-
   TODO: these are better names for theorems in init.logic.
-/

-- keep both
lemma implies_trans {p q r : Prop} (h₁ : implies p q) (h₂ : implies q r) : implies p r :=
implies.trans h₁ h₂

lemma not_intro {a : Prop} (h : a → false) : ¬ a :=
not.intro h

-- this is also called mt in init.logic. We can keep both.
lemma contrapos {a b : Prop} (h : a → b) (nb : ¬ b) : ¬ a :=
implies.resolve h nb

-- not_not_intro and non_contradictory_intro are the same.
-- I suggest keeping only the first.

-- maybe keep both names?
@[elab_as_eliminator]
lemma false_elim {c : Prop} (h : false) : c :=
false.elim h

-- parallels not_false_iff
lemma not_true_iff : (¬ true) ↔ false :=
not_true

lemma {u} id_def {A : Type u} (a : A) : id a = a := id.def a

-- should substr be marked as [elab_as_eliminator]?

def {u} ne_def {A : Type u} (a b : A) : ne a b = ¬ (a = b) := ne.def a b

section
universe variable u
variables {A : Type u} {a b : A}

lemma ne_intro (h : a = b → false) : a ≠ b := h

lemma ne_elim (h : a ≠ b) : a = b → false := h

lemma ne_irrefl (h : a ≠ a) : false := h rfl

lemma ne_symm (h : a ≠ b) : b ≠ a :=
assume (h₁ : b = a), h (eq.symm h₁)
end

-- similarly, we have heq_elim, heq_subst, heq_trans

section
variables {a b c d : Prop}

@[elab_as_eliminator]
lemma and_elim (h₁ : a ∧ b) (h₂ : a → b → c) : c :=
and.elim h₁ h₂

-- isn't symm better than swap?
lemma and_symm : a ∧ b → b ∧ a := and.swap

@[elab_as_eliminator]
lemma or_elim (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → c) : c :=
or.elim h₁ h₂ h₃

lemma not_not_em (a : Prop) : ¬¬(a ∨ ¬a) :=
non_contradictory_em a

lemma or_symm : a ∨ b → b ∨ a := or.swap

lemma iff_intro : (a → b) → (b → a) → (a ↔ b) := iff.intro

-- why does iff.elim switch the order of h₁ and h₂?
@[recursor 4]
lemma iff_elim (h₁ : a ↔ b) (h₂ : (a → b) → (b → a) → c) : c :=
iff.elim h₂ h₁

-- similarly, we have iff.intro, iff.elim, iff.elim_left, iff.mp,
-- iff.elim_right, iff.mpr, iff.refl, iff.rfl, iff.trans, iff.symm, iff.comm,
-- iff.of_eq

lemma not_not_not_iff (a : Prop) : ¬¬¬a ↔ ¬a :=
not_non_contradictory_iff_absurd a

-- similarly, imp_congr -> implies_congr, imp_congr_ctx -> implies_congr_ctx,
-- imp_congr_right -> implies_congr_right

lemma and_implies (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d := and.imp hac hbd

variables (a b c)

lemma and_comm : a ∧ b ↔ b ∧ a := and.comm

lemma and_assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := and.assoc

lemma and_left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) := and.left_comm

lemma and_right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
iff.trans (and_assoc a b c) (iff.trans (and_congr iff.rfl (and_comm _ _))
                                      (iff.symm (and_assoc _ _ _)))

variables {a b c d}

lemma or_implies_or (h₂ : a → c) (h₃ : b → d) : a ∨ b → c ∨ d := or.imp h₂ h₃

lemma or_implies_or_left (h : a → b) : a ∨ c → b ∨ c := or.imp_left h

lemma or_implies_or_right (h : a → b) : c ∨ a → c ∨ b := or.imp_right h

variables (a b c)

lemma or_comm : a ∨ b ↔ b ∨ a := or.comm

lemma or_assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) := or.assoc

lemma or_left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) := or.left_comm

lemma or_right_comm : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b :=
iff.trans (or_assoc a b c) (iff.trans (or_congr iff.rfl (or_comm _ _))
                                      (iff.symm (or_assoc _ _ _)))

-- similarly, or.resolve_left, or.neg_resolve_left, or.resolve_right, or.neg_resolve_right

def exists_intro := @exists.intro

def exists_elim := @exists.elim

attribute [intro]
lemma {u} exists_unique_intro {A : Type u} {p : A → Prop} (w : A)
    (h₁ : p w) (h₂ : ∀ y, p y → y = w) :
  ∃! x, p x :=
exists_unique.intro w h₁ h₂

end
