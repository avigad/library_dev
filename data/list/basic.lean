/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn

Basic properties of lists.
-/
import ...logic.basic

-- TODO(Jeremy): move to nat
namespace nat

theorem succ_inj {n m : ℕ} (h : succ n = succ m) : n = m :=
nat.no_confusion h id

end nat

open function nat

namespace list
universe variable u
variable {α : Type u}

attribute [simp]
lemma cons_ne_nil (a : α) (l : list α) : a::l ≠ [] :=
begin intro, contradiction end

lemma head_eq_of_cons_eq {α : Type} {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pheq)

lemma tail_eq_of_cons_eq {α : Type} {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pteq)

lemma cons_inj {α : Type} {a : α} : injective (cons a) :=
take l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

/- append -/

attribute [simp]
theorem append_nil_left (t : list α) : [] ++ t = t :=
rfl

attribute [simp]
theorem append_cons (x : α) (s t : list α) : (x::s) ++ t = x::(s ++ t) :=
rfl

attribute [simp]
theorem append_nil_right (t : list α) : t ++ [] = t :=
begin induction t with a t ih, reflexivity, simp [ih] end

attribute [simp]
theorem append.assoc (s t u : list α) : s ++ t ++ u = s ++ (t ++ u) :=
begin induction s with a s ih, reflexivity, simp [ih] end

/- length -/
attribute [simp]
theorem length_nil : length (@nil α) = 0 :=
rfl

attribute [simp]
theorem length_cons (x : α) (t : list α) : length (x::t) = length t + 1 :=
rfl

attribute [simp]
theorem length_append (s t : list α) : length (s ++ t) = length s + length t :=
begin induction s with a s ih, simp, simp [ih] end

theorem eq_nil_of_length_eq_zero : ∀ {l : list α}, length l = 0 → l = []
| []     h := rfl
| (a::s) h := by contradiction

theorem ne_nil_of_length_eq_succ : ∀ {l : list α} {n : nat}, length l = succ n → l ≠ []
| []     n h := by contradiction
| (a::l) n h := begin intro h, contradiction end

/- concat -/

attribute [simp]
theorem concat_nil (a : α) : concat [] a = [a] :=
rfl

attribute [simp]
theorem concat_cons (a b : α) (l : list α) : concat (a::l) b  = a::(concat l b) :=
rfl

attribute [simp]
theorem concat_eq_append (a : α) (l : list α) : concat l a = l ++ [a] :=
begin induction l with b l ih, simp, simp [ih] end

attribute [simp]
theorem concat_ne_nil (a : α) (l : list α) : concat l a ≠ [] :=
begin induction l, repeat { intro h, contradiction } end

attribute [simp]
theorem length_concat (a : α) (l : list α) : length (concat l a) = length l + 1 :=
begin rw [concat_eq_append, length_append], reflexivity end

attribute [simp]
theorem concat_append (a : α) (l₁ l₂ : list α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ :=
begin induction l₁ with b l₁ ih, simp, simp [ih] end

theorem append_concat (a : α) (l₁ l₂ : list α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a :=
begin induction l₂ with b l₂ ih, repeat { simp } end

/- last -/

definition last : Π l : list α, l ≠ [] → α
| []          h := absurd rfl h
| [a]         h := a
| (a₁::a₂::l) h := last (a₂::l) $ cons_ne_nil a₂ l

attribute [simp]
lemma last_singleton (a : α) (h : [a] ≠ []) : last [a] h = a :=
rfl

attribute [simp]
lemma last_cons_cons (a₁ a₂ : α) (l : list α) (h : a₁::a₂::l ≠ []) :
  last (a₁::a₂::l) h = last (a₂::l) (cons_ne_nil a₂ l) :=
rfl

theorem last_congr {l₁ l₂ : list α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
  last l₁ h₁ = last l₂ h₂ :=
by subst l₁


-- TODO(Jeremy): this was not easy. Is there are better proof? Can we automate it?
-- The commented-out version was "by rec_inst_simp"

attribute [simp]
theorem last_concat {a : α} (l : list α) : ∀ (h : concat l a ≠ []), last (concat l a) h = a :=
begin
  induction l with b l₁ ih,
  { intro h, reflexivity},
  induction l₁ with c l₂ ih',
  { intro h, reflexivity},
  rw [concat_cons, concat_cons], intro h, rw [last_cons_cons _ _ _ h],
  rw [last_congr (cons_ne_nil c (concat l₂ a)) (concat_ne_nil _ _) (concat_cons c a l₂)^.symm],
  rw ih
end

/- reverse -/

attribute [simp]
theorem reverse_nil : reverse (@nil α) = [] :=
rfl

attribute [simp]
theorem reverse_cons (a : α) (l : list α) : reverse (a::l) = concat (reverse l) a :=
have aux : ∀ l₁ l₂, reverse_core l₁ (concat l₂ a) = concat (reverse_core l₁ l₂) a,
  begin
    intros l₁, induction l₁ with b l₁ ih,
    { intro l₂, reflexivity },
    intro l₂, transitivity, apply (ih (b :: l₂)), reflexivity,
  end,
aux l nil

attribute [simp]
theorem reverse_singleton (a : α) : reverse [a] = [a] :=
rfl

attribute [simp]
theorem reverse_append (s t : list α) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
begin induction s with a s ih, simp, simp [ih] end

attribute [simp]
theorem reverse_reverse (l : list α) : reverse (reverse l) = l :=
begin induction l with a l ih, simp, simp [ih] end

theorem concat_eq_reverse_cons (a : α) (l : list α) : concat l a = reverse (a :: reverse l) :=
begin induction l with a l ih, simp, simp [ih] end

theorem length_reverse (l : list α) : length (reverse l) = length l :=
begin induction l with a l ih, simp, simp [ih] end

/- head and tail -/

attribute [simp]
theorem head_cons [h : inhabited α] (a : α) (l : list α) : head (a::l) = a :=
rfl

attribute [simp]
theorem head_append [h : inhabited α] (t : list α) {s : list α} (h : s ≠ []) :
  head (s ++ t) = head s :=
begin induction s with a s ih, contradiction, simp end

attribute [simp]
theorem tail_nil : tail (@nil α) = [] :=
rfl

attribute [simp]
theorem tail_cons (a : α) (l : list α) : tail (a::l) = l :=
rfl

theorem cons_head_tail [h : inhabited α] {l : list α} (h : l ≠ []) : (head l)::(tail l) = l :=
begin induction l with a l ih, contradiction, simp end

/- list membership -/

-- TODO(Jeremy): annotations are generally needed on ([] : list α). Can this be avoided?
-- Also, when the annotations are left out, the error message is inscrutible.

attribute [simp]
theorem mem_nil_iff (a : α) : a ∈ ([] : list α) ↔ false :=
iff.rfl

theorem not_mem_nil (a : α) : a ∉ ([] : list α) :=
iff.mp $ mem_nil_iff a

attribute [simp]
theorem mem_cons (a : α) (l : list α) : a ∈ a :: l :=
or.inl rfl

theorem mem_cons_of_mem (y : α) {a : α} {l : list α} : a ∈ l → a ∈ y :: l :=
assume H, or.inr H

theorem mem_cons_iff (a y : α) (l : list α) : a ∈ y::l ↔ (a = y ∨ a ∈ l) :=
iff.rfl

theorem eq_or_mem_of_mem_cons {a y : α} {l : list α} : a ∈ y::l → a = y ∨ a ∈ l :=
assume h, h

theorem mem_singleton {a b : α} : a ∈ [b] → a = b :=
suppose a ∈ [b], or.elim (eq_or_mem_of_mem_cons this)
  (suppose a = b, this)
  (suppose a ∈ ([] : list α), absurd this (not_mem_nil a))

theorem mem_of_mem_cons_of_mem {a b : α} {l : list α} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, or.elim (eq_or_mem_of_mem_cons ainbl)
  (suppose a = b, begin subst a, exact binl end)
  (suppose a ∈ l, this)

theorem mem_or_mem_of_mem_append {a : α} {s t : list α} : a ∈ s ++ t → a ∈ s ∨ a ∈ t :=
list.induction_on s or.inr
  (take b s,
    assume ih : a ∈ s ++ t → a ∈ s ∨ a ∈ t,
    suppose a ∈ b::s ++ t,
    have a = b ∨ a ∈ s ++ t, from this,
    have a = b ∨ a ∈ s ∨ a ∈ t, from or_of_or_of_implies_right this ih,
    show a ∈ b::s ∨ a ∈ t, from iff.mpr or.assoc this)

theorem mem_append_of_mem_or_mem {a : α} {s t : list α} : a ∈ s ∨ a ∈ t → a ∈ s ++ t :=
list.induction_on s
  (take h, or.elim h false.elim id)
  (take b s,
    assume ih : a ∈ s ∨ a ∈ t → a ∈ s ++ t,
    suppose a ∈ b::s ∨ a ∈ t,
      or.elim this
        (suppose a ∈ b::s,
          or.elim (eq_or_mem_of_mem_cons this)
            (suppose a = b, or.inl this)
            (suppose a ∈ s, or.inr (ih (or.inl this))))
        (suppose a ∈ t, or.inr (ih (or.inr this))))

theorem mem_append_iff (a : α) (s t : list α) : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t :=
iff.intro mem_or_mem_of_mem_append mem_append_of_mem_or_mem

theorem not_mem_of_not_mem_append_left {a : α} {s t : list α} : a ∉ s++t → a ∉ s :=
λ nainst ains, absurd (mem_append_of_mem_or_mem (or.inl ains)) nainst

theorem not_mem_of_not_mem_append_right {a : α} {s t : list α} : a ∉ s++t → a ∉ t :=
λ nainst aint, absurd (mem_append_of_mem_or_mem (or.inr aint)) nainst

theorem not_mem_append {a : α} {s t : list α} : a ∉ s → a ∉ t → a ∉ s++t :=
λ nains naint ainst, or.elim (mem_or_mem_of_mem_append ainst)
  (λ ains, by contradiction)
  (λ aint, by contradiction)

lemma length_pos_of_mem {a : α} : ∀ {l : list α}, a ∈ l → 0 < length l
| []     := suppose a ∈ ([] : list α), begin simp at this, contradiction end
| (b::l) := suppose a ∈ b::l, zero_lt_succ _

theorem mem_split {a : α} {l : list α} : a ∈ l → ∃ s t : list α, l = s ++ (a::t) :=
list.induction_on l
  (suppose a ∈ ([] : list α), begin simp at this, contradiction end)
  (take b l,
    assume ih : a ∈ l → ∃ s t : list α, l = s ++ (a::t),
    suppose a ∈ b::l,
    or.elim (eq_or_mem_of_mem_cons this)
      (suppose a = b, ⟨[], l, begin rw this, reflexivity end⟩)
      (suppose a ∈ l,
        match (ih this) with
        | ⟨s, t, (h : l = s ++ (a::t))⟩ := ⟨b::s, t, begin rw h, reflexivity end⟩
        end))

theorem mem_append_left {a : α} {l₁ : list α} (l₂ : list α) : a ∈ l₁ → a ∈ l₁ ++ l₂ :=
assume ainl₁, mem_append_of_mem_or_mem (or.inl ainl₁)

theorem mem_append_right {a : α} (l₁ : list α) {l₂ : list α} : a ∈ l₂ → a ∈ l₁ ++ l₂ :=
assume ainl₂, mem_append_of_mem_or_mem (or.inr ainl₂)

theorem mem_of_ne_of_mem {a y : α} {l : list α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
or.elim (eq_or_mem_of_mem_cons h₂) (λe, absurd e h₁) (λr, r)

theorem ne_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ≠ b :=
assume nin aeqb, absurd (or.inl aeqb) nin

theorem not_mem_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ∉ l :=
assume nin nainl, absurd (or.inr nainl) nin

lemma not_mem_cons_of_ne_of_not_mem {a y : α} {l : list α} : a ≠ y → a ∉ l → a ∉ y::l :=
assume P1 P2, not.intro (assume Pain, absurd (eq_or_mem_of_mem_cons Pain) (not_or P1 P2))

lemma ne_and_not_mem_of_not_mem_cons {a y : α} {l : list α} : a ∉ y::l → a ≠ y ∧ a ∉ l :=
assume P, and.intro (ne_of_not_mem_cons P) (not_mem_of_not_mem_cons P)

-- TODO(Jeremy): move this to data/list/set.lean

definition sublist (l₁ l₂ : list α) := ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance : has_subset (list α) := ⟨sublist⟩

attribute [simp]
theorem nil_sub (l : list α) : [] ⊆ l :=
λ b i, false.elim (iff.mp (mem_nil_iff b) i)

attribute [simp]
theorem sub.refl (l : list α) : l ⊆ l :=
λ b i, i

theorem sub.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
λ b i, h₂ (h₁ i)

attribute [simp]
theorem sub_cons (a : α) (l : list α) : l ⊆ a::l :=
λ b i, or.inr i

theorem sub_of_cons_sub {a : α} {l₁ l₂ : list α} : a::l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
λ s b i, s (mem_cons_of_mem _ i)

theorem cons_sub_cons  {l₁ l₂ : list α} (a : α) (s : l₁ ⊆ l₂) : (a::l₁) ⊆ (a::l₂) :=
λ b hin, or.elim (eq_or_mem_of_mem_cons hin)
  (λ e : b = a,  or.inl e)
  (λ i : b ∈ l₁, or.inr (s i))

attribute [simp]
theorem sub_append_left (l₁ l₂ : list α) : l₁ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (or.inl i)

attribute [simp]
theorem sub_append_right (l₁ l₂ : list α) : l₂ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (or.inr i)

theorem sub_cons_of_sub (a : α) {l₁ l₂ : list α} : l₁ ⊆ l₂ → l₁ ⊆ (a::l₂) :=
λ (s : l₁ ⊆ l₂) (a : α) (i : a ∈ l₁), or.inr (s i)

theorem sub_app_of_sub_left (l l₁ l₂ : list α) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₁) (a : α) (ainl : a ∈ l),
  have a ∈ l₁, from s ainl,
  mem_append_of_mem_or_mem (or.inl this)

theorem sub_app_of_sub_right (l l₁ l₂ : list α) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₂) (a : α) (ainl : a ∈ l),
  have a ∈ l₂, from s ainl,
  mem_append_of_mem_or_mem (or.inr this)

theorem cons_sub_of_sub_of_mem {a : α} {l m : list α} (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
take b, suppose b ∈ a::l,
or.elim (eq_or_mem_of_mem_cons this)
  (suppose b = a, begin subst b, exact ainm end)
  (suppose b ∈ l, lsubm this)

theorem app_sub_of_sub_of_sub {l₁ l₂ l : list α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
take a, suppose a ∈ l₁ ++ l₂,
or.elim (mem_or_mem_of_mem_append this)
  (suppose a ∈ l₁, l₁subl this)
  (suppose a ∈ l₂, l₂subl this)

/- find -/

section find
variable [decidable_eq α]

definition find : α → list α → nat
| a []       := 0
| a (b :: l) := if a = b then 0 else succ (find a l)

attribute [simp]
theorem find_nil (a : α) : find a [] = 0 :=
rfl

theorem find_cons (a b : α) (l : list α) : find a (b::l) = if a = b then 0 else succ (find a l) :=
rfl

attribute [simp]
theorem find_cons_of_eq {a b : α} (l : list α) : a = b → find a (b::l) = 0 :=
assume e, if_pos e

attribute [simp]
theorem find_cons_of_ne {a b : α} (l : list α) : a ≠ b → find a (b::l) = succ (find a l) :=
assume n, if_neg n

attribute [simp]
theorem find_of_not_mem {l : list α} {a : α} : ¬a ∈ l → find a l = length l :=
list.induction_on l
   (suppose ¬a ∈ ([] : list α), rfl)
   (take b l,
      assume ih : ¬a ∈ l → find a l = length l,
      suppose ¬a ∈ b::l,
      have ¬a = b ∧ ¬a ∈ l, begin rw [mem_cons_iff, not_or_iff] at this, exact this end,
      show find a (b::l) = length (b::l),
        begin rw [find_cons, if_neg this^.left, ih this^.right], reflexivity end)

lemma find_le_length {a : α} {l : list α} : find a l ≤ length l :=
list.induction_on l
  (by simp)
  (take b l, assume ih : find a l ≤ length l,
   show find a (b::l) ≤ length (b::l), from
     decidable.by_cases
       (suppose a = b, begin simp [this, find_cons_of_eq l (eq.refl b)], apply zero_le end)
       (suppose a ≠ b, begin simp [this, find_cons_of_ne l this], apply succ_le_succ ih end))

lemma not_mem_of_find_eq_length : ∀ {a : α} {l : list α}, find a l = length l → a ∉ l
| a []        := by simp
| a (b::l)    := begin
                   note h := decidable.em (a = b),
                   cases h with aeqb aneb,
                   { rw [find_cons_of_eq l aeqb, length_cons], intros, contradiction },
                   rw [find_cons_of_ne l aneb, length_cons, mem_cons_iff, not_or_iff],
                   intro h, split, assumption,
                   exact not_mem_of_find_eq_length (nat.succ_inj h)
                 end

lemma find_lt_length {a} {l : list α} (al : a ∈ l) : find a l < length l :=
begin
  apply lt_of_le_of_ne,
  apply find_le_length,
  apply not.intro, intro Peq,
  exact absurd al (not_mem_of_find_eq_length Peq)
end

end find

/- nth element -/
section nth
attribute [simp]
theorem nth_zero (a : α) (l : list α) : nth (a :: l) 0 = some a :=
rfl

attribute [simp]
theorem nth_succ (a : α) (l : list α) (n : nat) : nth (a::l) (succ n) = nth l n :=
rfl

theorem nth_eq_some : ∀ {l : list α} {n : nat}, n < length l → Σ a : α, nth l n = some a
| ([] : list α) n h := absurd h (not_lt_zero _)
| (a::l) 0        h := ⟨a, rfl⟩
| (a::l) (succ n) h :=
  have n < length l, from lt_of_succ_lt_succ h,
  sigma.rec_on (nth_eq_some this)
    (take b : α, take hb : nth l n = some b,
      show Σ b : α, nth (a::l) (succ n) = some b,
         from sigma.mk b (by rw [nth_succ, hb]))

theorem find_nth [decidable_eq α] {a : α} : ∀ {l : list α}, a ∈ l → nth l (find a l) = some a
| []     ain   := absurd ain (not_mem_nil _)
| (b::l) ainbl := decidable.by_cases
  (λ aeqb : a = b, by rewrite [find_cons_of_eq _ aeqb, nth_zero, aeqb])
  (λ aneb : a ≠ b, or.elim (eq_or_mem_of_mem_cons ainbl)
    (λ aeqb : a = b, absurd aeqb aneb)
    (λ ainl : a ∈ l, by rewrite [find_cons_of_ne _ aneb, nth_succ, find_nth ainl]))

definition inth [h : inhabited α] (l : list α) (n : nat) : α :=
match (nth l n) with
| (some a) := a
| none     := arbitrary α
end

theorem inth_zero [inhabited α] (a : α) (l : list α) : inth (a :: l) 0 = a :=
rfl

theorem inth_succ [inhabited α] (a : α) (l : list α) (n : nat) : inth (a::l) (n+1) = inth l n :=
rfl

end nth

section ith

definition ith : Π (l : list α) (i : nat), i < length l → α
| nil       i        h := absurd h (not_lt_zero i)
| (a::ains) 0        h := a
| (a::ains) (succ i) h := ith ains i (lt_of_succ_lt_succ h)

attribute [simp]
lemma ith_zero (a : α) (l : list α) (h : 0 < length (a::l)) : ith (a::l) 0 h = a :=
rfl

attribute [simp]
lemma ith_succ (a : α) (l : list α) (i : nat) (h : succ i < length (a::l))
                      : ith (a::l) (succ i) h = ith l i (lt_of_succ_lt_succ h) :=
rfl
end ith

-- TODO(Jeremy): move this to set?

/- quasiequal a l l' means that l' is exactly l, with a added
   once somewhere -/
section qeq

inductive qeq (a : α) : list α → list α → Prop
| qhead : ∀ l, qeq l (a::l)
| qcons : ∀ (b : α) {l l' : list α}, qeq l l' → qeq (b::l) (b::l')

open qeq

notation l' `≈`:50 a `|` l:50 := qeq a l l'

theorem qeq_app : ∀ (l₁ : list α) (a : α) (l₂ : list α), l₁ ++ (a :: l₂) ≈ a | l₁ ++ l₂
| ([] : list α) b l₂ := qhead b l₂
| (a::ains)     b l₂ := qcons a (qeq_app ains b l₂)

theorem mem_head_of_qeq {a : α} : ∀ {l₁ l₂ : list α}, l₁ ≈ a | l₂ → a ∈ l₁
| ._ ._ (qhead .a l)            := mem_cons a l
| ._ ._ (@qcons .α .a b l l' q) := mem_cons_of_mem b (mem_head_of_qeq q)

theorem mem_tail_of_qeq {a : α} : ∀ {l₁ l₂ : list α}, l₁ ≈ a | l₂ → ∀ {b}, b ∈ l₂ → b ∈ l₁
| ._ ._ (qhead .a l)            b bl  := mem_cons_of_mem a bl
| ._ ._ (@qcons .α .a c l l' q) b bcl :=
  or.elim (eq_or_mem_of_mem_cons bcl)
    (take bc : b = c,
      begin rw bc, apply mem_cons end)
    (take bl : b ∈ l,
      have bl' : b ∈ l', from mem_tail_of_qeq q bl,
      mem_cons_of_mem c bl')

theorem mem_cons_of_qeq {a : α} : ∀ {l₁ l₂ : list α}, l₁≈a|l₂ → ∀ {b}, b ∈ l₁ → b ∈ a::l₂
| ._ ._ (qhead .a l)            b bal                  := bal
| ._ ._ (@qcons .α .a c l l' q) b (bcl' : b ∈ c :: l') :=
  show b ∈ a :: c :: l, from
    or.elim (eq_or_mem_of_mem_cons bcl')
      (take bc : b = c,
        begin rw bc, apply mem_cons_of_mem, apply mem_cons end)
      (take bl' : b ∈ l',
        have b ∈ a :: l, from mem_cons_of_qeq q bl',
        or.elim (eq_or_mem_of_mem_cons this)
          (take ba : b = a,
            begin rw ba, apply mem_cons end)
          (take bl : b ∈ l,
            mem_cons_of_mem a (mem_cons_of_mem c bl)))

theorem length_eq_of_qeq {a : α} {l₁ l₂ : list α} : l₁ ≈ a | l₂ → length l₁ = succ (length l₂) :=
begin
  intro q, induction q with l b l l' q ih, simp, reflexivity, simp, rw ih, reflexivity
end

theorem qeq_of_mem {a : α} {l : list α} : a ∈ l → (∃ l', l ≈ a | l') :=
list.induction_on l
  (λ h : a ∈ (nil : list α), absurd h (not_mem_nil a))
  (λ b bs r ainbbs, or.elim (eq_or_mem_of_mem_cons ainbbs)
    (λ aeqb  : a = b,
       have ∃ l, b::bs ≈ b | l, from
         exists.intro bs (qhead b bs),
       begin rw aeqb, exact this end)
    (λ ainbs : a ∈ bs,
       have ∃ l', bs ≈ a|l', from r ainbs,
       exists.elim this (take (l' : list α) (q : bs ≈ a|l'),
         have b::bs ≈ a | b::l', from qcons b q,
         exists.intro (b::l') this)))

theorem qeq_split {a : α} : ∀ {l l' : list α}, l'≈a|l → ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l' = l₁ ++ (a::l₂)
| ._ ._ (qhead .a l)            := ⟨([] : list α), l, by simp⟩
| ._ ._ (@qcons .α .a c l l' q) :=
  match (qeq_split q) with
  | ⟨l₁, l₂, h₁, h₂⟩ := ⟨c :: l₁, l₂, by simp [h₁, h₂]⟩
  end

theorem subset_of_mem_of_subset_of_qeq {a : α} {l : list α} {u v : list α} :
  a ∉ l → a::l ⊆ v → v≈a|u → l ⊆ u :=
λ (nainl : a ∉ l) (s : a::l ⊆ v) (q : v≈a|u) (b : α) (binl : b ∈ l),
  have b ∈ v,    from s (or.inr binl),
  have b ∈ a::u, from mem_cons_of_qeq q this,
  or.elim (eq_or_mem_of_mem_cons this)
    (suppose b = a, begin subst b, contradiction end)
    (suppose b ∈ u, this)

end qeq

section firstn

definition firstn : nat → list α → list α
| 0     l      := []
| (n+1) []     := []
| (n+1) (a::l) := a :: firstn n l

attribute [simp]
lemma firstn_zero : ∀ (l : list α), firstn 0 l = [] :=
begin intros, reflexivity end

attribute [simp]
lemma firstn_nil : ∀ n, firstn n [] = ([] : list α)
| 0     := rfl
| (n+1) := rfl

lemma firstn_cons : ∀ n (a : α) (l : list α), firstn (succ n) (a::l) = a :: firstn n l :=
begin intros, reflexivity end

lemma firstn_all : ∀ (l : list α), firstn (length l) l = l
| []     := rfl
| (a::l) := begin change a :: (firstn (length l) l) = a :: l, rw firstn_all end

lemma firstn_all_of_ge : ∀ {n} {l : list α}, n ≥ length l → firstn n l = l
| 0     []     h := rfl
| 0     (a::l) h := absurd h (not_le_of_gt (zero_lt_succ _))
| (n+1) []     h := rfl
| (n+1) (a::l) h :=
  begin
    change a :: firstn n l = a :: l,
    rw [firstn_all_of_ge (le_of_succ_le_succ h)]
  end

-- TODO(Jeremy): restore when we have min
/-
lemma firstn_firstn : ∀ (n m) (l : list α), firstn n (firstn m l) = firstn (min n m) l
| n         0        l      := sorry -- by rewrite [min_zero, firstn_zero, firstn_nil]
| 0         m        l      := sorry -- by rewrite [zero_min]
| (succ n)  (succ m) nil    := sorry -- by rewrite [*firstn_nil]
| (succ n)  (succ m) (a::l) := sorry -- by rewrite [*firstn_cons, firstn_firstn, min_succ_succ]
-/

lemma length_firstn_le : ∀ (n) (l : list α), length (firstn n l) ≤ n
| 0        l      := begin rw [firstn_zero], reflexivity end
| (succ n) (a::l) := begin
                       rw [firstn_cons, length_cons], apply succ_le_succ,
                       apply length_firstn_le
                     end
| (succ n) []     := begin rewrite [firstn_nil, length_nil], apply zero_le end

-- TODO(Jeremy): restore when we have min
/-
lemma length_firstn_eq : ∀ (n) (l : list α), length (firstn n l) = min n (length l)
| 0        l      := sorry -- by rewrite [firstn_zero, zero_min]
| (succ n) (a::l) := sorry -- by rewrite [firstn_cons, *length_cons, *add_one, min_succ_succ,
                                          length_firstn_eq]
| (succ n) []     := sorry -- by rewrite [firstn_nil]
-/
end firstn

-- TODO(Jeremy): restore when we have nat.sub
/-
section dropn
-- 'dropn n l' drops the first 'n' elements of 'l'

theorem length_dropn
: ∀ (i : ℕ) (l : list α), length (dropn i l) = length l - i
| 0 l := rfl
| (succ i) [] := calc
  length (dropn (succ i) []) = 0 - succ i : sorry -- by rewrite (nat.zero_sub (succ i))
| (succ i) (x::l) := calc
  length (dropn (succ i) (x::l))
          = length (dropn i l)       : by reflexivity
      ... = length l - i             : length_dropn i l
      ... = succ (length l) - succ i : sorry -- by rewrite (succ_sub_succ (length l) i)
end dropn
-/

section count
variable [decidable_eq α]

definition count (a : α) : list α → nat
| []      := 0
| (x::xs) := if a = x then succ (count xs) else count xs

lemma count_nil (a : α) : count a [] = 0 :=
rfl

lemma count_cons (a b : α) (l : list α) :
  count a (b :: l) = if a = b then succ (count a l) else count a l :=
rfl

lemma count_cons_eq (a : α) (l : list α) : count a (a::l) = succ (count a l) :=
if_pos rfl

lemma count_cons_of_ne {a b : α} (h : a ≠ b) (l : list α) : count a (b::l) = count a l :=
if_neg h

lemma count_cons_ge_count (a b : α) (l : list α) : count a (b :: l) ≥ count a l :=
decidable.by_cases
  (suppose a = b, begin subst b, rewrite count_cons_eq, apply le_succ end)
  (suppose a ≠ b, begin rw (count_cons_of_ne this), apply le_refl end)

lemma count_singleton (a : α) : count a [a] = 1 :=
begin rw count_cons_eq, reflexivity end

lemma count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂
| []      l₂ := begin rw [append_nil_left, count_nil, zero_add] end
| (b::l₁) l₂ := decidable.by_cases
  (suppose a = b, by rw [-this, append_cons, count_cons_eq, count_cons_eq, succ_add, count_append])
  (suppose a ≠ b, by rw [append_cons, count_cons_of_ne this, count_cons_of_ne this, count_append])

lemma count_concat (a : α) (l : list α) : count a (concat l a) = succ (count a l) :=
begin rw [concat_eq_append, count_append, count_singleton], reflexivity end

lemma mem_of_count_gt_zero : ∀ {a : α} {l : list α}, count a l > 0 → a ∈ l
| a []     h := absurd h (lt_irrefl _)
| a (b::l) h := decidable.by_cases
  (suppose a = b, begin subst b, apply mem_cons end)
  (suppose a ≠ b,
   have count a l > 0, begin rw [count_cons_of_ne this] at h, exact h end,
   have a ∈ l,    from mem_of_count_gt_zero this,
   show a ∈ b::l, from mem_cons_of_mem _ this)

-- TODO(Jeremy): install transitivity rule for ≥, >
/-
lemma count_gt_zero_of_mem : ∀ {a : α} {l : list α}, a ∈ l → count a l > 0
| a []     h := absurd h (not_mem_nil _)
| a (b::l) h := or.elim h
  (suppose a = b, begin subst b, rw count_cons_eq, apply zero_lt_succ end)
  (suppose a ∈ l, calc
   count a (b::l) ≥ count a l : count_cons_ge_count _ _
           ...    > 0         : count_gt_zero_of_mem this)
-/

lemma count_eq_zero_of_not_mem {a : α} {l : list α} (h : a ∉ l) : count a l = 0 :=
have ∀ n, count a l = n → count a l = 0,
  begin
    intro n, cases n,
     { intro this, exact this },
    intro this, exact absurd (mem_of_count_gt_zero (begin rw this, exact dec_trivial end)) h
  end,
this (count a l) rfl

end count
end list
