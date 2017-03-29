/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Theorems that require decidability hypotheses are in the namespace "decidable".
Classical versions are in the namespace "classical".

Note: in the presence of automation, this whole file may be unnecessary. On the other hand,
maybe it is useful for writing automation.
-/

/-
    propositional connectives
-/

section propositional
variables {a b c d : Prop}

/- implies -/

theorem contrapos {a b : Prop} (h : a → b) : ¬ b → ¬ a :=
λ hnb ha, hnb (h ha)

theorem implies_self (h : a) : a := h

theorem implies_intro (h : a) (h₂ : b) : a := h

theorem true_implies_iff (a : Prop) : (true → a) ↔ a :=
iff.intro (assume H, H trivial) implies_intro

theorem implies_false_iff (a : Prop) : (a → false) ↔ ¬ a := iff.rfl

/- not -/

theorem {u} not_elim {A : Sort u} (H1 : ¬a) (H2 : a) : A := absurd H2 H1

theorem not_not_of_not_implies : ¬(a → b) → ¬¬a :=
contrapos not_elim

theorem not_of_not_implies : ¬(a → b) → ¬b :=
contrapos implies_intro

theorem decidable.not_not_iff (a : Prop) [decidable a] : ¬¬a ↔ a :=
iff.intro decidable.by_contradiction not_not_intro

theorem decidable.not_not_elim {a : Prop} [decidable a] : ¬¬a → a :=
decidable.by_contradiction

theorem decidable.of_not_implies [decidable a] (h : ¬ (a → b)) : a :=
decidable.by_contradiction (not_not_of_not_implies h)

/- and -/

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) :=
contrapos and.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) :=
contrapos and.right

theorem and_implies_left (h : a → b) : a ∧ c → b ∧ c :=
and_implies h implies_self

theorem and_implies_right (h : a → b) : c ∧ a → c ∧ b :=
and_implies implies_self h

theorem and_of_and_of_implies_of_implies (h₁ : a ∧ b) (h₂ : a → c) (h₃ : b → d) : c ∧ d :=
and_implies h₂ h₃ h₁

theorem and_of_and_of_imp_left (h₁ : a ∧ c) (h : a → b) : b ∧ c :=
and_implies_left h h₁

theorem and_of_and_of_imp_right (h₁ : c ∧ a) (h : a → b) : c ∧ b :=
and_implies_right h h₁

theorem and_imp_iff (a b c : Prop) : (a ∧ b → c) ↔ (a → b → c) :=
iff.intro (λ h a b, h ⟨a, b⟩) and.rec

theorem and_not_self_iff (a : Prop) : a ∧ ¬ a ↔ false :=
iff.intro (assume h, (h^.right) (h^.left)) (assume h, h^.elim)

theorem not_and_self_iff (a : Prop) : ¬ a ∧ a ↔ false :=
iff.intro (assume ⟨hna, ha⟩, hna ha) false.elim

/- or -/

theorem or_of_or_of_implies_of_implies (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d :=
or.imp h₂ h₃ h₁

theorem or_of_or_of_implies_left (h₁ : a ∨ c) (h : a → b) : b ∨ c :=
or.imp_left h h₁

theorem or_of_or_of_implies_right (h₁ : c ∨ a) (h : a → b) : c ∨ b :=
or.imp_right h h₁

theorem or.elim3 (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
or.elim h ha (assume h₂, or.elim h₂ hb hc)

theorem or_resolve_right (h₁ : a ∨ b) (h₂ : ¬a) : b :=
or.elim h₁ (not_elim h₂) implies_self

theorem or_resolve_left (h₁ : a ∨ b) (h₂ : ¬b) : a :=
or_resolve_right h₁^.symm h₂

theorem or_implies_distrib (a b c : Prop) : ((a ∨ b) → c) ↔ ((a → c) ∧ (b → c)) :=
iff.intro
  (λh, and.intro (implies.trans or.inl h) (implies.trans or.inr h))
  (and.rec or.rec)

theorem or_iff_right_of_imp (ha : a → b) : (a ∨ b) ↔ b :=
iff.intro (or.rec ha implies_self) or.inr

theorem or_iff_left_of_imp (hb : b → a) : (a ∨ b) ↔ a :=
iff.intro (or.rec implies_self hb) or.inl

theorem or_iff_or (h1 : a ↔ c) (h2 : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
iff.intro (or.imp (iff.mp h1) (iff.mp h2)) (or.imp (iff.mpr h1) (iff.mpr h2))

theorem decidable.or_not_self_iff (a : Prop) [decidable a] : a ∨ ¬ a ↔ true :=
iff.intro (assume h, trivial) (assume h, decidable.em a)

theorem decidable.not_or_self_iff (a : Prop) [decidable a] : ¬ a ∨ a ↔ true :=
iff.intro (assume h, trivial) (assume h, (decidable.em a)^.symm)

/- distributivity -/

theorem and_distrib (a b c : Prop) : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
iff.intro
  (and.rec (λh, or.imp (and.intro h) (and.intro h)))
  (or.rec (and_implies_right or.inl) (and_implies_right or.inr))

theorem and_distrib_right (a b c : Prop) : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) :=
iff.trans (iff.trans and.comm (and_distrib c a b)) (or_iff_or and.comm and.comm)

theorem or_distrib (a b c : Prop) : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
iff.intro
  (or.rec (λh, and.intro (or.inl h) (or.inl h)) (and_implies or.inr or.inr))
  (and.rec (or.rec (implies.trans or.inl implies_intro)
           (implies.trans and.intro or.imp_right)))

theorem or_distrib_right (a b c : Prop) : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
iff.trans (iff.trans or.comm (or_distrib c a b))
          (and_congr or.comm or.comm)

/- iff -/

theorem implies_iff {a : Prop} (n : Prop) (ha : a) : (a → b) ↔ b :=
iff.intro (λf, f ha) implies_intro

theorem decidable.not_or_of_implies [decidable a] (h : a → b) : ¬ a ∨ b :=
if ha : a then or.inr (h ha) else or.inl ha

theorem implies_of_not_or (h : ¬ a ∨ b) : a → b :=
assume ha,
or.elim h (assume hna, absurd ha hna) (assume hb, hb)

theorem decidable.implies_iff_not_or (a b : Prop) [decidable a] : (a → b) ↔ (¬ a ∨ b) :=
iff.intro decidable.not_or_of_implies implies_of_not_or

theorem not_implies_of_and_not (h : a ∧ ¬ b) : ¬ (a → b) :=
assume h₁, and.right h (h₁ (and.left h))

theorem decidable.and_not_of_not_implies [decidable a] (h : ¬ (a → b)) : a ∧ ¬ b :=
⟨decidable.of_not_implies h, not_of_not_implies h⟩

theorem decidable.not_implies_iff_and_not (a b : Prop) [decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
iff.intro decidable.and_not_of_not_implies not_implies_of_and_not

theorem decidable.peirce (a b : Prop) [decidable a] : ((a → b) → a) → a :=
if ha : a then λ h, ha else λ h, h (λ h', absurd h' ha)

/- de morgan's laws -/

theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

theorem decidable.not_or_not_of_not_and [decidable a] (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
if ha : a then
  or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
else
  or.inl ha

theorem decidable.not_or_not_of_not_and' [decidable b] (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
if hb : b then
  or.inl (show ¬ a, from assume ha, h ⟨ha, hb⟩)
else
  or.inr hb

theorem decidable.not_and_iff (a b : Prop) [decidable a] : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
iff.intro decidable.not_or_not_of_not_and not_and_of_not_or_not

theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
assume h₁, or.elim h₁ (assume ha, and.left h ha) (assume hb, and.right h hb)

theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
iff.intro not_and_not_of_not_or not_or_of_not_and_not

theorem decidable.or_iff_not_and_not (a b : Prop) [decidable a] [decidable b] :
  a ∨ b ↔ ¬ (¬a ∧ ¬b) :=
by rewrite [-not_or_iff, decidable.not_not_iff]

theorem decidable.and_iff_not_or_not (a b : Prop) [decidable a] [decidable b] :
  a ∧ b ↔ ¬ (¬ a ∨ ¬ b) :=
by rewrite [-decidable.not_and_iff, decidable.not_not_iff]

end propositional

/- classical versions -/

namespace classical
variables {a b c d : Prop}

local attribute [instance] prop_decidable

theorem not_not_iff (a : Prop)  : ¬¬a ↔ a :=
decidable.not_not_iff a

theorem not_not_elim {a : Prop}  : ¬¬a → a :=
decidable.not_not_elim

theorem of_not_implies (h : ¬ (a → b)) : a :=
decidable.of_not_implies h

theorem or_not_self_iff (a : Prop) : a ∨ ¬ a ↔ true :=
decidable.or_not_self_iff a

theorem not_or_self_iff (a : Prop) : ¬ a ∨ a ↔ true :=
decidable.not_or_self_iff a

theorem not_or_of_implies (h : a → b) : ¬ a ∨ b :=
decidable.not_or_of_implies h

theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
decidable.implies_iff_not_or a b

theorem and_not_of_not_implies (h : ¬ (a → b)) : a ∧ ¬ b :=
decidable.and_not_of_not_implies h

theorem not_implies_iff_and_not (a b : Prop) : ¬(a → b) ↔ a ∧ ¬b :=
decidable.not_implies_iff_and_not a b

theorem peirce (a b : Prop) : ((a → b) → a) → a :=
decidable.peirce a b

theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
decidable.not_or_not_of_not_and h

theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
decidable.not_and_iff a b

theorem or_iff_not_and_not (a b : Prop) : a ∨ b ↔ ¬ (¬a ∧ ¬b) :=
decidable.or_iff_not_and_not a b

theorem and_iff_not_or_not (a b : Prop) : a ∧ b ↔ ¬ (¬ a ∨ ¬ b) :=
decidable.and_iff_not_or_not a b

end classical


/-
  quantifiers
-/

section quantifiers
universe variable u
variables {A : Type u} {p q : A → Prop} {b : Prop}

theorem forall_of_forall (h : ∀ x, (p x → q x)) (h₁ : ∀ x, p x) : ∀ x, q x :=
take x, h x (h₁ x)

theorem exists_of_exists (h : ∀ x, (p x → q x)) (h₁ : ∃ x, p x) : ∃ x, q x :=
match h₁ with ⟨x, hpx⟩ := ⟨x, h x hpx⟩ end

theorem forall_implies_of_exists_implies (h : (∃ x, p x) → b) : ∀ x, p x → b :=
take x, assume hpx, h ⟨x, hpx⟩

theorem exists_implies_of_forall_implies (h : ∀ x, p x → b) : (∃ x, p x) → b :=
Exists.rec h

theorem exists_implies_distrib (p : A → Prop) (b : Prop) : ((∃ x, p x) → b) ↔ (∀ x, p x → b) :=
iff.intro forall_implies_of_exists_implies exists_implies_of_forall_implies

--theorem forall_not_of_not_exists (h : ¬ ∃ x, p x) : ∀ x, ¬ p x :=
--forall_implies_of_exists_implies h

theorem not_exists_of_forall_not (h : ∀ x, ¬ p x) : ¬ ∃ x, p x :=
exists_implies_of_forall_implies h

theorem not_exists_iff_forall_not (p : A → Prop) : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
exists_implies_distrib p false

theorem decidable.exists_not_of_not_forall [decidable (∃ x, ¬ p x)] [∀ x, decidable (p x)]
  (h : ¬ ∀ x, p x) : ∃ x, ¬ p x :=
decidable.by_contradiction
  (assume h₁, h (take x, decidable.by_contradiction (assume hnpx, h₁ ⟨x, hnpx⟩)))

theorem not_forall_of_exists_not (h : ∃ x, ¬ p x) : ¬ ∀ x, p x :=
assume h₁, match h with ⟨x, hnpx⟩ := hnpx (h₁ x) end

theorem decidable.not_forall_iff_exists_not (p : A → Prop)
    [decidable (∃ x, ¬ p x)] [∀ x, decidable (p x)] :
  (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
iff.intro decidable.exists_not_of_not_forall not_forall_of_exists_not

theorem forall_true_iff : (∀ x : A, true) ↔ true :=
iff_true_intro (λ h, trivial)

theorem forall_p_iff_p (A : Type u) [inhabited A] (p : Prop) : (∀ x : A, p) ↔ p :=
iff.intro (λ h, h (inhabited.default A)) (λ hp x, hp)

theorem exists_p_iff_p (A : Type u) [inhabited A] (p : Prop) : (∃ x : A, p) ↔ p :=
iff.intro (Exists.rec (λ x (hpx : p), hpx)) (λ hp, ⟨default A, hp⟩)

theorem forall_and_distrib (p q : A → Prop) : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume h, ⟨(take x, (h x)^.left), (take x, (h x)^.right)⟩)
  (assume h x, ⟨h^.left x, h^.right x⟩)

theorem exists_or_distrib (p q : A → Prop) : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
  (assume ⟨x, hpq⟩, or.elim hpq (assume hpx, or.inl (exists.intro x hpx))
                               (assume hqx, or.inr (exists.intro x hqx)))
  (assume hepq,
    or.elim hepq
      (assume hepx,
         match hepx : _ → ∃ x, p x ∨ q x with ⟨x, hpx⟩  := ⟨x, or.inl hpx⟩ end)
      (assume ⟨x, hqx⟩, ⟨x, or.inr hqx⟩))

@[simp]
theorem exists_and_iff_and_exists {q : Prop} {p : A → Prop} :
  (∃x, q ∧ p x) ↔ q ∧ (∃x, p x) :=
⟨take ⟨x, hq, hp⟩, ⟨hq, x, hp⟩, take ⟨hq, x, hp⟩, ⟨x, hq, hp⟩⟩

end quantifiers

/- classical versions -/

namespace classical
universe variable u
variables {A : Type u} {p : A → Prop}

local attribute [instance] prop_decidable

theorem exists_not_of_not_forall (h : ¬ ∀ x, p x) : ∃ x, ¬ p x :=
decidable.exists_not_of_not_forall h

theorem not_forall_iff_exists_not (p : A → Prop) : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
decidable.not_forall_iff_exists_not p

theorem forall_or_iff_or_forall {q : Prop} {p : A → Prop} :
  (∀x, q ∨ p x) ↔ q ∨ (∀x, p x) :=
⟨take h, if hq : q then or.inl hq else or.inr $ take x, or.resolve_left (h x) hq, 
  take h x, or.imp_right (suppose ∀x, p x, this x) h⟩

end classical


/-
   bounded quantifiers
-/

section bounded_quantifiers
universe variable u
variables {A : Type u} {r p q : A → Prop} {b : Prop}

theorem bforall_congr (h : ∀ x (hrx : r x), p x ↔ q x) :
  (∀ x (hrx : r x), p x) ↔ (∀ x (hrx : r x), q x) :=
begin
  apply forall_congr,
  intro x,
  apply forall_congr,
  apply h
end

theorem bexists_congr (h : ∀ x (hrx : r x), p x ↔ q x) :
  (∃ x (hrx : r x), p x) ↔ (∃ x (hrx : r x), q x) :=
begin
  apply exists_congr,
  intros,
  apply exists_congr,
  apply h
end

theorem bforall_of_bforall (h : ∀ x (hrx : r x), (p x → q x)) (h₁ : ∀ x (hrx : r x), p x) :
  ∀ x (hrx : r x) , q x :=
take x, assume hrx, h x hrx (h₁ x hrx)

theorem bexists_of_bexists {A : Type} {p q : A → Prop}
    (h : ∀ x, (p x → q x)) (h₁ : ∃ x, p x) : ∃ x, q x :=
match h₁ with ⟨x, hpx⟩ := ⟨x, h x hpx⟩ end

theorem bforall_of_forall (h : ∀ x, p x) : ∀ x (hrx : r x), p x :=
λ x hrx, h x

theorem forall_of_bforall (h : ∀ x (ht : true), p x) : ∀ x, p x :=
λ x, h x trivial

theorem bexists_of_exists (h : ∃ x, p x) : ∃ x (ht : true), p x :=
match h with ⟨x, hpx⟩ := ⟨x, trivial, hpx⟩ end

theorem exists_of_bexists (h : ∃ x (hrx : r x), p x) : ∃ x, p x :=
match h with ⟨x, hrx, hpx⟩ := ⟨x, hpx⟩ end

theorem bforall_implies_of_bexists_implies (h : (∃ x (hrx : r x), p x) → b) :
  ∀ x (hrx : r x), p x → b :=
λ x hrx hpx, h ⟨x, hrx, hpx⟩

theorem bexists_implies_of_bforall_implies (h : ∀ x (hrx : r x), p x → b) :
  (∃ x (hrx : r x), p x) → b :=
assume ⟨x, hrx, hpx⟩, h x hrx hpx

theorem bexists_implies_distrib (r p : A → Prop) (b : Prop) :
  ((∃ x (hrx : r x), p x) → b) ↔ (∀ x (hrx : r x), p x → b) :=
iff.intro bforall_implies_of_bexists_implies bexists_implies_of_bforall_implies

theorem bforall_not_of_not_bexists (h : ¬ ∃ x (hrx : r x), p x) : ∀ x (hrx : r x), ¬ p x :=
bforall_implies_of_bexists_implies h

theorem not_bexists_of_bforall_not (h : ∀ x (hrx : r x), ¬ p x) : ¬ ∃ x (hrx : r x), p x :=
bexists_implies_of_bforall_implies h

theorem not_bexists_iff_bforall_not (r p : A → Prop) :
  (¬ ∃ x (hrx : r x) , p x) ↔ (∀ x (h : r x), ¬ p x) :=
bexists_implies_distrib r p false

theorem decidable.bexists_not_of_not_bforall
    [decidable (∃ x (hrx : r x), ¬ p x)] [∀ x, decidable (p x)]
  (h : ¬ ∀ x (hrx : r x), p x) : ∃ x (hr : r x), ¬ p x :=
decidable.by_contradiction
  (assume h₁, h (take x, assume hrx, decidable.by_contradiction (assume hnpx, h₁ ⟨x, hrx, hnpx⟩)))

theorem not_bforall_of_bexists_not (h : ∃ x (hrx : r x), ¬ p x) : ¬ ∀ x (hrx : r x), p x :=
assume h₁, match h with ⟨x, hrx, hnpx⟩ := hnpx (h₁ x hrx) end

theorem decidable.not_bforall_iff_bexists_not (r p : A → Prop)
    [decidable (∃ x (hrx : r x), ¬ p x)] [∀ x, decidable (p x)] :
  (¬ ∀ x (hrx : r x), p x) ↔ (∃ x (hrx : r x), ¬ p x) :=
iff.intro decidable.bexists_not_of_not_bforall not_bforall_of_bexists_not

theorem bforall_true_iff (r : A → Prop): (∀ x (hrx : r x), true) ↔ true :=
iff_true_intro (λ h hrx, trivial)

theorem bforall_and_distrib : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume h, ⟨(take x, (h x)^.left), (take x, (h x)^.right)⟩)
  (assume h x, ⟨h^.left x, h^.right x⟩)

theorem bexists_or_distrib (r p q : A → Prop) :
  (∃ x (hrx : r x), p x ∨ q x) ↔ (∃ x (hrx : r x), p x) ∨ (∃ x (hrx : r x), q x) :=
iff.intro
  (assume ⟨x, hrx, hpq⟩, or.elim hpq (assume hpx, or.inl (exists.intro x (exists.intro hrx hpx)))
                               (assume hqx, or.inr (exists.intro x (exists.intro hrx hqx))))
  (assume hepq,
    or.elim hepq
      (assume hepx,
         match hepx : _ → ∃ x (hrx : r x), p x ∨ q x with ⟨x, hrx, hpx⟩ := ⟨x, hrx, or.inl hpx⟩ end)
      (assume ⟨x, hrx, hqx⟩, ⟨x, hrx, or.inr hqx⟩))

end bounded_quantifiers

-- TODO(Jeremy): merge with previous section

section
  universe variable uu
  variables {α : Type uu} {p q : α → Prop}

  @[simp]
  theorem exists_prop_iff (p q : Prop) : (∃ h : p, q) ↔ p ∧ q :=
  iff.intro
    begin intro h', cases h', split, repeat { assumption } end
    begin intro h', cases h', split, repeat { assumption } end

  theorem bexists.elim {b : Prop} (h : ∃ x : α, ∃ h : p x, q x) (h' : ∀ (a : α), p a → q a → b) :
    b :=
  exists.elim h (λ a h₁, exists.elim h₁ (h' a))

  theorem bexists.intro (a : α) (h₁ : p a) (h₂ : q a) : ∃ x, ∃ h : p x, q x :=
  exists.intro a (exists.intro h₁ h₂)
end

namespace classical
universe variable u
variables {A : Type u} {r p : A → Prop}

local attribute [instance] prop_decidable
theorem bexists_not_of_not_bforall (h : ¬ ∀ x (hrx : r x), p x) : ∃ x (hr : r x), ¬ p x :=
decidable.bexists_not_of_not_bforall h

theorem not_bforall_iff_bexists_not (r p : A → Prop) :
  (¬ ∀ x (hrx : r x), p x) ↔ (∃ x (hrx : r x), ¬ p x) :=
decidable.not_bforall_iff_bexists_not r p

end classical
