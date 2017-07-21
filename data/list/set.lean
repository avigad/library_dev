/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

Set-like operations on lists.
-/

import data.list.basic data.list.comb .basic .comb
open nat function decidable

universe variables uu vv
variables {α : Type uu} {β : Type vv}

namespace list

section insert
variable [decidable_eq α]

@[simp]
theorem insert_nil (a : α) : insert a nil = [a] := rfl

theorem insert.def (a : α) (l : list α) : insert a l = if a ∈ l then l else concat l a := rfl

@[simp]
theorem insert_of_mem {a : α} {l : list α} (h : a ∈ l) : insert a l = l :=
by rw [insert.def, if_pos h]

@[simp]
theorem insert_of_not_mem {a : α} {l : list α} (h : a ∉ l) : insert a l = concat l a :=
by rw [insert.def, if_neg h]

@[simp]
theorem mem_insert_self (a : α) (l : list α) : a ∈ insert a l :=
by by_cases a ∈ l with h; simp [h]

@[simp]
theorem mem_insert_of_mem {a b : α} {l : list α} (h : a ∈ l) : a ∈ insert b l :=
by by_cases b ∈ l with h'; simp [h, h']

theorem eq_or_mem_of_mem_insert {a b : α} {l : list α} (h : a ∈ insert b l) : a = b ∨ a ∈ l :=
if h' : b ∈ l then
  begin simp [h'] at h, simp [h] end
else
  begin simp [h'] at h, assumption end

@[simp]
theorem mem_insert_iff (a b : α) (l : list α) : a ∈ insert b l ↔ a = b ∨ a ∈ l :=
iff.intro eq_or_mem_of_mem_insert
  (λ h, or.elim h (begin intro h', simp [h'] end) mem_insert_of_mem)

@[simp]
theorem length_insert_of_mem {a : α} [decidable_eq α] {l : list α} (h : a ∈ l) :
  length (insert a l) = length l :=
by simp [h]

@[simp]
theorem length_insert_of_not_mem {a : α} [decidable_eq α] {l : list α} (h : a ∉ l) :
  length (insert a l) = length l + 1 :=
by simp [h]

theorem forall_mem_insert_of_forall_mem {p : α → Prop} {a : α} {l : list α}
   (h₁ : p a) (h₂ : ∀ x ∈ l, p x) :
  ∀ x ∈ insert a l, p x :=
if h : a ∈ l then begin simp [h], exact h₂ end
else begin simp [h], intros b hb, cases hb with h₃ h₃, {rw h₃, assumption}, exact h₂ _ h₃ end

end insert

section erase
variable [decidable_eq α]

@[simp]
lemma erase_nil (a : α) : [].erase a = [] :=
rfl

lemma erase_cons (a b : α) (l : list α) : (b :: l).erase a = if b = a then l else b :: l.erase a :=
rfl

@[simp]
lemma erase_cons_head (a : α) (l : list α) : (a :: l).erase a = l :=
by simp [erase_cons, if_pos]

@[simp]
lemma erase_cons_tail {a b : α} (l : list α) (h : b ≠ a) : (b::l).erase a = b :: l.erase a :=
by simp [erase_cons, if_neg, h]

@[simp]
lemma length_erase_of_mem {a : α} : ∀{l:list α}, a ∈ l → length (l.erase a) = pred (length l)
| []         h := rfl
| [x]        h := begin simp at h, simp [h] end
| (x::y::xs) h := if h' : x = a then
                    by simp [h', one_add]
                  else
                    have ainyxs : a ∈ y::xs, from or_resolve_right h $ by cc,
                    by simp [h', length_erase_of_mem ainyxs, one_add]

@[simp]
lemma erase_of_not_mem {a : α} : ∀{l : list α}, a ∉ l → l.erase a = l
| []      h  := rfl
| (x::xs) h  :=
  have anex   : x ≠ a,  from λ aeqx  : x = a,  absurd (or.inl aeqx.symm) h,
  have aninxs : a ∉ xs, from λ ainxs : a ∈ xs, absurd (or.inr ainxs) h,
  by simp [anex, erase_of_not_mem aninxs]

lemma erase_append_left {a : α} : ∀ {l₁:list α} (l₂), a ∈ l₁ → (l₁++l₂).erase a = l₁.erase a ++ l₂
| []      l₂  h := absurd h (not_mem_nil a)
| (x::xs) l₂  h := if h' : x = a then by simp [h']
                   else
                     have a ∈ xs, from mem_of_ne_of_mem (assume h, h' h.symm) h,
                     by simp [erase_append_left l₂ this, h']

lemma erase_append_right {a : α} : ∀{l₁ : list α} (l₂), a ∉ l₁ → (l₁++l₂).erase a = l₁ ++ l₂.erase a
| []      l₂ h := rfl
| (x::xs) l₂ h := if h' : x = a then begin simp [h'] at h, contradiction end
                  else
                    have a ∉ xs, from not_mem_of_not_mem_cons h,
                    by simp [erase_append_right l₂ this, h']

lemma erase_sublist (a : α) : ∀(l : list α), l.erase a <+ l
| []        := sublist.refl nil
| (x :: xs) := if h : x = a then
                 by simp [h]
               else
                 begin simp [h], apply cons_sublist_cons, apply erase_sublist xs end

lemma erase_subset (a : α) (l : list α) : l.erase a ⊆ l :=
subset_of_sublist (erase_sublist a l)

theorem mem_erase_of_ne_of_mem {a b : α} : ∀ {l : list α}, a ≠ b → a ∈ l → a ∈ l.erase b
| []       aneb anil := begin simp at anil, contradiction end
| (c :: l) aneb acl  := if h : c = b then
                         begin simp [h, aneb] at acl, simp [h, acl] end
                        else
                          begin
                            simp [h], simp at acl, cases acl with h' h',
                            { simp [h'] },
                            simp [mem_erase_of_ne_of_mem aneb h']
                          end

theorem mem_of_mem_erase {a b : α} : ∀{l:list α}, a ∈ l.erase b → a ∈ l
| []       h := begin simp at h, contradiction end
| (c :: l) h := if h' : c = b then
                  begin simp [h'] at h, simp [h] end
                else
                  begin
                    simp [h'] at h, cases h with h'' h'',
                    { simp [h''] },
                    simp [mem_of_mem_erase h'']
                  end
end erase

/- disjoint -/
section disjoint

def disjoint (l₁ l₂ : list α) : Prop := ∀ ⦃a⦄, (a ∈ l₁ → a ∈ l₂ → false)

lemma disjoint_left {l₁ l₂ : list α} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₁ → a ∉ l₂ :=
λ d, d

lemma disjoint_right {l₁ l₂ : list α} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₂ → a ∉ l₁ :=
λ d a i₂ i₁, d i₁ i₂

lemma disjoint.comm {l₁ l₂ : list α} : disjoint l₁ l₂ → disjoint l₂ l₁ :=
λ d a i₂ i₁, d i₁ i₂

lemma disjoint_of_subset_left {l₁ l₂ l : list α} : l₁ ⊆ l → disjoint l l₂ → disjoint l₁ l₂ :=
λ ss d x xinl₁, d (ss xinl₁)

lemma disjoint_of_subset_right {l₁ l₂ l : list α} : l₂ ⊆ l → disjoint l₁ l → disjoint l₁ l₂ :=
λ ss d x xinl xinl₁, d xinl (ss xinl₁)

lemma disjoint_of_disjoint_cons_left {a : α} {l₁ l₂} : disjoint (a::l₁) l₂ → disjoint l₁ l₂ :=
disjoint_of_subset_left (list.subset_cons _ _)

lemma disjoint_of_disjoint_cons_right {a : α} {l₁ l₂} : disjoint l₁ (a::l₂) → disjoint l₁ l₂ :=
disjoint_of_subset_right (list.subset_cons _ _)

lemma disjoint_nil_left (l : list α) : disjoint [] l :=
λ a ab, absurd ab (not_mem_nil a)

lemma disjoint_nil_right (l : list α) : disjoint l [] :=
disjoint.comm (disjoint_nil_left l)

lemma disjoint_cons_of_not_mem_of_disjoint {a : α} {l₁ l₂ : list α} :
  a ∉ l₂ → disjoint l₁ l₂ → disjoint (a::l₁) l₂ :=
λ nainl₂ d x (xinal₁ : x ∈ a::l₁),
  or.elim (eq_or_mem_of_mem_cons xinal₁)
    (λ xeqa  : x = a, eq.symm xeqa ▸ nainl₂)
    (λ xinl₁ : x ∈ l₁, disjoint_left d xinl₁)

lemma disjoint_append_of_disjoint_left {l₁ l₂ l : list α} :
  disjoint l₁ l → disjoint l₂ l → disjoint (l₁++l₂) l :=
λ d₁ d₂ x h, or.elim (mem_or_mem_of_mem_append h) (@d₁ x) (@d₂ x)

lemma disjoint_of_disjoint_append_left_left {l₁ l₂ l : list α} : disjoint (l₁++l₂) l → disjoint l₁ l :=
disjoint_of_subset_left (list.subset_append_left _ _)

lemma disjoint_of_disjoint_append_left_right {l₁ l₂ l : list α} : disjoint (l₁++l₂) l → disjoint l₂ l :=
disjoint_of_subset_left (list.subset_append_right _ _)

lemma disjoint_of_disjoint_append_right_left {l₁ l₂ l : list α} : disjoint l (l₁++l₂) → disjoint l l₁ :=
disjoint_of_subset_right (list.subset_append_left _ _)

lemma disjoint_of_disjoint_append_right_right {l₁ l₂ l : list α} : disjoint l (l₁++l₂) → disjoint l l₂ :=
disjoint_of_subset_right (list.subset_append_right _ _)

end disjoint

/- upto -/
def upto : nat → list nat
| 0     := []
| (n+1) := n :: upto n

@[simp]
theorem upto_nil  : upto 0 = nil := rfl

@[simp]
theorem upto_succ (n : nat) : upto (succ n) = n :: upto n := rfl

@[simp]
theorem length_upto : ∀ n, length (upto n) = n
| 0        := rfl
| (succ n) := begin rw [upto_succ, length_cons, length_upto] end

theorem upto_ne_nil_of_ne_zero {n : ℕ} (h : n ≠ 0) : upto n ≠ nil :=
assume : upto n = nil,
have upto n = upto 0, from upto_nil ▸ this,
have n = 0, from calc
     n = length (upto n) : by rw length_upto
   ... = length (upto 0) : by rw this
   ... = 0               : by rw length_upto,
h this

theorem lt_of_mem_upto : ∀ ⦃n i⦄, i ∈ upto n → i < n
| 0        := assume i imem, absurd imem (not_mem_nil _)
| (succ n) := assume i imem,
              or.elim (eq_or_mem_of_mem_cons imem)
                (λ h, begin rw h, apply lt_succ_self end)
                (λ h, lt.trans (lt_of_mem_upto h) (lt_succ_self n))

theorem mem_upto_succ_of_mem_upto {n i : nat} : i ∈ upto n → i ∈ upto (succ n) :=
assume i, mem_cons_of_mem _ i

theorem mem_upto_of_lt : ∀ ⦃n i : nat⦄, i < n → i ∈ upto n
| 0        := λ i h, absurd h (not_lt_zero i)
| (succ n) := λ i h,
begin
  cases nat.lt_or_eq_of_le (le_of_lt_succ h) with ilt ieq,
  { apply mem_upto_succ_of_mem_upto, apply mem_upto_of_lt ilt },
  simp [ieq]
end

lemma upto_step : ∀ (n : nat), upto (succ n) = (map succ (upto n)) ++ [0]
| 0        := rfl
| (succ n) := by simp [(upto_step n)^.symm]

/- union -/
section union
variable [decidable_eq α]

@[simp]
theorem union_nil (l : list α) : l ∪ [] = l := rfl

@[simp]
theorem union_cons (l₁ l₂ : list α) (a : α) : l₁ ∪ (a :: l₂) = insert a l₁ ∪ l₂ := rfl

theorem mem_or_mem_of_mem_union : ∀ {l₁ l₂ : list α} {a : α}, a ∈ l₁ ∪ l₂ → a ∈ l₁ ∨ a ∈ l₂
| l₁ []        a h := begin simp at h, simp [h] end
| l₁ (b :: l₂) a h :=
  if h' : b ∈ l₂ then
    begin
      simp at h,
      cases mem_or_mem_of_mem_union h with h₀ h₀,
      { simp at h₀, cases h₀ with h₁ h₁, simp [h₁], simp [h₁] },
      simp [h₀]
    end
  else
    begin
      simp [union_cons] at h,
      cases mem_or_mem_of_mem_union h with h₀ h₀,
      { simp at h₀, cases h₀ with h₁ h₁, repeat { simp [h₁] } },
      simp [h₀]
    end

theorem mem_union_left {a : α} {l₁ : list α} (h : a ∈ l₁) (l₂ : list α) : a ∈ l₁ ∪ l₂ :=
begin
  induction l₂ with b l₂ ih generalizing l₁,
  { simp [h] },
  { apply ih, simp [h] }
end

theorem mem_union_right {a : α} (l₁ : list α) {l₂ : list α} (h : a ∈ l₂) : a ∈ l₁ ∪ l₂ :=
begin
  induction l₂ with b l₂ ih generalizing l₁,
  { simp at h, contradiction },
  simp, simp at h,
  cases h with h₀ h₀,
  { subst h₀, apply mem_union_left, simp },
  apply ih h₀
end

@[simp]
theorem mem_union_iff (a : α) (l₁ l₂ : list α) : a ∈ l₁ ∪ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ :=
iff.intro mem_or_mem_of_mem_union (λ h, or.elim h (λ h', mem_union_left h' l₂) (mem_union_right l₁))

theorem forall_mem_union {p : α → Prop} {l₁ l₂ : list α} (h₁ : ∀ x ∈ l₁, p x) (h₂ : ∀ x ∈ l₂, p x) :
  ∀ x ∈ l₁ ∪ l₂, p x :=
begin
  intro x, simp, intro h, cases h,
  { apply h₁, assumption },
  apply h₂, assumption
end

theorem forall_mem_of_forall_mem_union_left {p : α → Prop} {l₁ l₂ : list α}
   (h : ∀ x ∈ l₁ ∪ l₂, p x) :
  ∀ x ∈ l₁, p x :=
begin intros x xl₁, apply h, apply mem_union_left xl₁ end

theorem forall_mem_of_forall_mem_union_right {p : α → Prop} {l₁ l₂ : list α}
   (h : ∀ x ∈ l₁ ∪ l₂, p x) :
  ∀ x ∈ l₂, p x :=
begin intros x xl₂, apply h, apply mem_union_right l₁ xl₂ end

end union

/- inter -/
section inter
variable [decidable_eq α]

@[simp]
theorem inter_nil (l : list α) : [] ∩ l = [] := rfl

@[simp]
theorem inter_cons_of_mem {a : α} (l₁ : list α) {l₂ : list α} (h : a ∈ l₂) :
  (a::l₁) ∩ l₂ = a :: (l₁ ∩ l₂) :=
if_pos h

@[simp]
theorem inter_cons_of_not_mem {a : α} (l₁ : list α) {l₂ : list α} (h : a ∉ l₂) :
  (a::l₁) ∩ l₂ = l₁ ∩ l₂ :=
if_neg h

theorem mem_of_mem_inter_left : ∀ {l₁ l₂ : list α} {a : α}, a ∈ l₁ ∩ l₂ → a ∈ l₁
| []      l₂ a i := absurd i (not_mem_nil a)
| (b::l₁) l₂ a i := by_cases
  (λ binl₂  : b ∈ l₂,
    have aux : a ∈ b :: l₁ ∩ l₂, begin rw [inter_cons_of_mem _ binl₂] at i, exact i end,
    or.elim (eq_or_mem_of_mem_cons aux)
      (λ aeqb : a = b, begin rw [aeqb], apply mem_cons_self end)
      (λ aini, mem_cons_of_mem _ (mem_of_mem_inter_left aini)))
  (λ nbinl₂ : b ∉ l₂,
    have ainl₁ : a ∈ l₁,
      begin rw [inter_cons_of_not_mem _ nbinl₂] at i, exact (mem_of_mem_inter_left i) end,
    mem_cons_of_mem _ ainl₁)

theorem mem_of_mem_inter_right : ∀ {l₁ l₂ : list α} {a : α}, a ∈ l₁ ∩ l₂ → a ∈ l₂
| []      l₂ a i := absurd i (not_mem_nil _)
| (b::l₁) l₂ a i := by_cases
  (λ binl₂  : b ∈ l₂,
    have aux : a ∈ b :: l₁ ∩ l₂, begin rw [inter_cons_of_mem _ binl₂] at i, exact i end,
    or.elim (eq_or_mem_of_mem_cons aux)
      (λ aeqb : a = b, begin rw [aeqb], exact binl₂ end)
      (λ aini : a ∈ l₁ ∩ l₂, mem_of_mem_inter_right aini))
  (λ nbinl₂ : b ∉ l₂,
    begin rw [inter_cons_of_not_mem _ nbinl₂] at i, exact (mem_of_mem_inter_right i) end)

theorem mem_inter_of_mem_of_mem : ∀ {l₁ l₂ : list α} {a : α}, a ∈ l₁ → a ∈ l₂ → a ∈ l₁ ∩ l₂
| []      l₂ a i₁ i₂ := absurd i₁ (not_mem_nil _)
| (b::l₁) l₂ a i₁ i₂ := by_cases
  (λ binl₂  : b ∈ l₂,
    or.elim (eq_or_mem_of_mem_cons i₁)
      (λ aeqb  : a = b,
        begin rw [inter_cons_of_mem _ binl₂, aeqb], apply mem_cons_self end)
     (λ ainl₁ : a ∈ l₁,
        begin
          rw [inter_cons_of_mem _ binl₂],
          apply mem_cons_of_mem,
          exact (mem_inter_of_mem_of_mem ainl₁ i₂)
        end))
  (λ nbinl₂ : b ∉ l₂,
    or.elim (eq_or_mem_of_mem_cons i₁)
     (λ aeqb  : a = b,
       begin rw aeqb at i₂, exact absurd i₂ nbinl₂ end)
     (λ ainl₁ : a ∈ l₁,
       begin rw [inter_cons_of_not_mem _ nbinl₂], exact (mem_inter_of_mem_of_mem ainl₁ i₂) end))

@[simp]
theorem mem_inter_iff (a : α) (l₁ l₂ : list α) : a ∈ l₁ ∩ l₂ ↔ a ∈ l₁ ∧ a ∈ l₂ :=
iff.intro
  (λ h, and.intro (mem_of_mem_inter_left h) (mem_of_mem_inter_right h))
  (λ h, mem_inter_of_mem_of_mem h^.left h^.right)

theorem inter_eq_nil_of_disjoint : ∀ {l₁ l₂ : list α}, disjoint l₁ l₂ → l₁ ∩ l₂ = []
| []      l₂ d := rfl
| (a::l₁) l₂ d :=
  have aux_eq : l₁ ∩ l₂ = [], from inter_eq_nil_of_disjoint (disjoint_of_disjoint_cons_left d),
  have nainl₂ : a ∉ l₂,       from disjoint_left d (mem_cons_self _ _),
  by rw [inter_cons_of_not_mem _ nainl₂, aux_eq]

theorem forall_mem_inter_of_forall_left {p : α → Prop} {l₁ : list α} (h : ∀ x ∈ l₁, p x)
     (l₂ : list α) :
  ∀ x, x ∈ l₁ ∩ l₂ → p x :=
λ x xl₁l₂, h x (mem_of_mem_inter_left xl₁l₂)

theorem forall_mem_inter_of_forall_right {p : α → Prop} (l₁ : list α) {l₂ : list α}
    (h : ∀ x ∈ l₂, p x) :
  ∀ x, x ∈ l₁ ∩ l₂ → p x :=
λ x xl₁l₂, h x (mem_of_mem_inter_right xl₁l₂)

end inter

/- no duplicates predicate -/

inductive nodup {α : Type uu} : list α → Prop
| ndnil  : nodup []
| ndcons : ∀ {a : α} {l : list α}, a ∉ l → nodup l → nodup (a::l)

section nodup
open nodup

theorem nodup_nil : @nodup α [] :=
ndnil

theorem nodup_cons {a : α} {l : list α} : a ∉ l → nodup l → nodup (a::l)  :=
λ i n, ndcons i n

theorem nodup_singleton (a : α) : nodup [a] :=
nodup_cons (not_mem_nil a) nodup_nil

theorem nodup_of_nodup_cons : ∀ {a : α} {l : list α}, nodup (a::l) → nodup l
| a xs (ndcons i n) := n

theorem not_mem_of_nodup_cons : ∀ {a : α} {l : list α}, nodup (a::l) → a ∉ l
| a xs (ndcons i n) := i

theorem not_nodup_cons_of_mem {a : α} {l : list α} : a ∈ l → ¬ nodup (a :: l) :=
λ ainl d, absurd ainl (not_mem_of_nodup_cons d)

theorem nodup_of_sublist : Π {l₁ l₂ : list α}, l₁ <+ l₂ → nodup l₂ → nodup l₁
| ._ ._ sublist.slnil h := h
| ._ ._ (sublist.cons l₁ l₂ a s) (ndcons i n) := nodup_of_sublist s n
| ._ ._ (sublist.cons2 l₁ l₂ a s) (ndcons i n) :=
  ndcons (λh, i (subset_of_sublist s h)) (nodup_of_sublist s n)

theorem not_nodup_cons_of_not_nodup {a : α} {l : list α} : ¬ nodup l → ¬ nodup (a :: l) :=
mt nodup_of_nodup_cons

theorem nodup_of_nodup_append_left {l₁ l₂ : list α} : nodup (l₁++l₂) → nodup l₁ :=
nodup_of_sublist (sublist_append_left l₁ l₂)

theorem nodup_of_nodup_append_right : ∀ {l₁ l₂ : list α}, nodup (l₁++l₂) → nodup l₂
| []      l₂ n := n
| (x::xs) l₂ n := nodup_of_nodup_append_right (nodup_of_nodup_cons n)

theorem disjoint_of_nodup_append : ∀ {l₁ l₂ : list α}, nodup (l₁++l₂) → disjoint l₁ l₂
| []      l₂  d := disjoint_nil_left l₂
| (x::xs) l₂  d :=
  have nodup (x::(xs++l₂)),    from d,
  have x ∉ xs++l₂,             from not_mem_of_nodup_cons this,
  have nxinl₂ : x ∉ l₂,        from not_mem_of_not_mem_append_right this,
  assume a, assume : a ∈ x::xs,
    or.elim (eq_or_mem_of_mem_cons this)
      (assume : a = x, eq.symm this ▸ nxinl₂)
      (assume ainxs : a ∈ xs,
        have nodup (x::(xs++l₂)), from d,
        have nodup (xs++l₂),      from nodup_of_nodup_cons this,
        have disjoint xs l₂,      from disjoint_of_nodup_append this,
        disjoint_left this ainxs)

theorem nodup_append_of_nodup_of_nodup_of_disjoint :
  ∀ {l₁ l₂ : list α}, nodup l₁ → nodup l₂ → disjoint l₁ l₂ → nodup (l₁++l₂)
| []      l₂ d₁ d₂ dsj := begin rw [nil_append], exact d₂ end
| (x::xs) l₂ d₁ d₂ dsj :=
  have ndxs     : nodup xs,            from nodup_of_nodup_cons d₁,
  have disjoint xs l₂,                 from disjoint_of_disjoint_cons_left dsj,
  have ndxsl₂   : nodup (xs++l₂),      from nodup_append_of_nodup_of_nodup_of_disjoint ndxs d₂ this,
  have nxinxs   : x ∉ xs,              from not_mem_of_nodup_cons d₁,
  have x ∉ l₂,                         from disjoint_left dsj (mem_cons_self x xs),
  have x ∉ xs++l₂,                     from not_mem_append nxinxs this,
  nodup_cons this ndxsl₂

theorem nodup_app_comm {l₁ l₂ : list α} (d : nodup (l₁++l₂)) : nodup (l₂++l₁) :=
have d₁  : nodup l₁,       from nodup_of_nodup_append_left d,
have d₂  : nodup l₂,       from nodup_of_nodup_append_right d,
have dsj : disjoint l₁ l₂, from disjoint_of_nodup_append d,
nodup_append_of_nodup_of_nodup_of_disjoint d₂ d₁ (disjoint.comm dsj)

theorem nodup_head {a : α} {l₁ l₂ : list α} (d : nodup (l₁++(a::l₂))) : nodup (a::(l₁++l₂)) :=
have d₁    : nodup (a::(l₂++l₁)), from nodup_app_comm d,
have d₂    : nodup (l₂++l₁),      from nodup_of_nodup_cons d₁,
have d₃    : nodup (l₁++l₂),      from nodup_app_comm d₂,
have nain  : a ∉ l₂++l₁,          from not_mem_of_nodup_cons d₁,
have nain₂ : a ∉ l₂,              from not_mem_of_not_mem_append_left nain,
have nain₁ : a ∉ l₁,              from not_mem_of_not_mem_append_right nain,
nodup_cons (not_mem_append nain₁ nain₂) d₃

theorem nodup_middle {a : α} {l₁ l₂ : list α} (d : nodup (a::(l₁++l₂))) : nodup (l₁++(a::l₂)) :=
have d₁    : nodup (l₁++l₂),      from nodup_of_nodup_cons d,
have nain  : a ∉ l₁++l₂,          from not_mem_of_nodup_cons d,
have disj  : disjoint l₁ l₂,      from disjoint_of_nodup_append d₁,
have d₂    : nodup l₁,            from nodup_of_nodup_append_left d₁,
have d₃    : nodup l₂,            from nodup_of_nodup_append_right d₁,
have nain₂ : a ∉ l₂,              from not_mem_of_not_mem_append_right nain,
have nain₁ : a ∉ l₁,              from not_mem_of_not_mem_append_left nain,
have d₄    : nodup (a::l₂),       from nodup_cons nain₂ d₃,
have disj₂ : disjoint l₁ (a::l₂), from disjoint.comm (disjoint_cons_of_not_mem_of_disjoint nain₁
                                           (disjoint.comm disj)),
nodup_append_of_nodup_of_nodup_of_disjoint d₂ d₄ disj₂

theorem nodup_map {f : α → β} (inj : injective f) : ∀ {l : list α}, nodup l → nodup (map f l)
| []      n := begin apply nodup_nil end
| (x::xs) n :=
  have nxinxs : x ∉ xs,           from not_mem_of_nodup_cons n,
  have ndxs   : nodup xs,         from nodup_of_nodup_cons n,
  have ndmfxs : nodup (map f xs), from nodup_map ndxs,
  have nfxinm : f x ∉ map f xs,   from
    λ ab : f x ∈ map f xs,
      match (exists_of_mem_map ab) with
      | ⟨(y : α), (yinxs : y ∈ xs), (fyfx : f y = f x)⟩ :=
        have yeqx : y = x, from inj fyfx,
        begin subst y, contradiction end
      end,
  nodup_cons nfxinm ndmfxs

theorem nodup_erase_of_nodup [decidable_eq α] (a : α) : ∀ {l}, nodup l → nodup (l.erase a)
| []     n := nodup_nil
| (b::l) n := by_cases
  (λ aeqb : b = a, begin rw [aeqb, erase_cons_head], exact (nodup_of_nodup_cons n) end)
  (λ aneb : b ≠ a,
    have nbinl   : b ∉ l,                  from not_mem_of_nodup_cons n,
    have ndl     : nodup l,                from nodup_of_nodup_cons n,
    have ndeal   : nodup (l.erase a),      from nodup_erase_of_nodup ndl,
    have nbineal : b ∉ l.erase a,          from λ i, absurd (erase_subset _ _ i) nbinl,
    have aux   : nodup (b :: l.erase a),   from nodup_cons nbineal ndeal,
    begin rw [erase_cons_tail _ aneb], exact aux end)

theorem mem_erase_of_nodup [decidable_eq α] (a : α) : ∀ {l}, nodup l → a ∉ l.erase a
| []     n := (not_mem_nil _)
| (b::l) n :=
  have ndl     : nodup l,       from nodup_of_nodup_cons n,
  have naineal : a ∉ l.erase a, from mem_erase_of_nodup ndl,
  have nbinl   : b ∉ l,         from not_mem_of_nodup_cons n,
  by_cases
  (λ aeqb : b = a, begin rw [aeqb.symm, erase_cons_head], exact nbinl end)
  (λ aneb : b ≠ a,
    have aux : a ∉ b :: l.erase a, from
      assume ainbeal : a ∈ b :: l.erase a, or.elim (eq_or_mem_of_mem_cons ainbeal)
        (λ aeqb   : a = b, absurd aeqb.symm aneb)
        (λ aineal : a ∈ l.erase a, absurd aineal naineal),
    begin rw [erase_cons_tail _ aneb], exact aux end)

def erase_dup [decidable_eq α] : list α → list α
| []        :=  []
| (x :: xs) :=  if x ∈ xs then erase_dup xs else x :: erase_dup xs

theorem erase_dup_nil [decidable_eq α] : erase_dup [] = ([] : list α) := rfl

theorem erase_dup_cons_of_mem [decidable_eq α] {a : α} {l : list α} :
  a ∈ l → erase_dup (a::l) = erase_dup l :=
assume ainl, calc
  erase_dup (a::l) = if a ∈ l then erase_dup l else a :: erase_dup l : rfl
              ...  = erase_dup l                                     : if_pos ainl

theorem erase_dup_cons_of_not_mem [decidable_eq α] {a : α} {l : list α} :
  a ∉ l → erase_dup (a::l) = a :: erase_dup l :=
assume nainl, calc
  erase_dup (a::l) = if a ∈ l then erase_dup l else a :: erase_dup l : rfl
              ...  = a :: erase_dup l                                : if_neg nainl

theorem mem_erase_dup [decidable_eq α] {a : α} : ∀ {l : list α}, a ∈ l → a ∈ erase_dup l
| []     h  := absurd h (not_mem_nil _)
| (b::l) h  := by_cases
  (λ binl  : b ∈ l, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb : a = b,
      begin rw [erase_dup_cons_of_mem binl], rw ←aeqb at binl, exact (mem_erase_dup binl) end)
    (λ ainl : a ∈ l,
      begin rw [erase_dup_cons_of_mem binl], exact (mem_erase_dup ainl) end))
  (λ nbinl : b ∉ l, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb : a = b,
      begin rw [erase_dup_cons_of_not_mem nbinl, aeqb], apply mem_cons_self end)
    (λ ainl : a ∈ l,
      begin rw [erase_dup_cons_of_not_mem nbinl], exact (or.inr (mem_erase_dup ainl)) end))

theorem erase_dup_sublist [decidable_eq α] : ∀ (l : list α), erase_dup l <+ l
| []     := sublist.slnil
| (b::l) := if h : b ∈ l then
    by simp[erase_dup, h]; exact sublist_cons_of_sublist _ (erase_dup_sublist l)
  else
    by simp[erase_dup, h]; exact cons_sublist_cons _ (erase_dup_sublist l)

theorem mem_of_mem_erase_dup [decidable_eq α] {a : α} : ∀ {l : list α}, a ∈ erase_dup l → a ∈ l
| []     h := begin rw [erase_dup_nil] at h, exact h end
| (b::l) h := by_cases
  (λ binl  : b ∈ l,
    have h₁ : a ∈ erase_dup l,
      begin rw [erase_dup_cons_of_mem binl] at h, exact h end,
    or.inr (mem_of_mem_erase_dup h₁))
  (λ nbinl : b ∉ l,
    have h₁ : a ∈ b :: erase_dup l,
      begin rw [erase_dup_cons_of_not_mem nbinl] at h, exact h end,
    or.elim (eq_or_mem_of_mem_cons h₁)
      (λ aeqb  : a = b, begin rw aeqb, apply mem_cons_self end)
      (λ ainel : a ∈ erase_dup l, or.inr (mem_of_mem_erase_dup ainel)))

@[simp]
theorem mem_erase_dup_iff [decidable_eq α] (a : α) (l : list α) : a ∈ erase_dup l ↔ a ∈ l :=
iff.intro mem_of_mem_erase_dup mem_erase_dup

theorem erase_dup_sub [decidable_eq α] (l : list α) : erase_dup l ⊆ l :=
λ a i, mem_of_mem_erase_dup i

theorem sub_erase_dup [decidable_eq α] (l : list α) : l ⊆ erase_dup l :=
λ a i, mem_erase_dup i

theorem nodup_erase_dup [decidable_eq α] : ∀ l : list α, nodup (erase_dup l)
| []        := begin rw erase_dup_nil, exact nodup_nil end
| (a::l)    := by_cases
  (λ ainl  : a ∈ l, begin rw [erase_dup_cons_of_mem ainl], exact (nodup_erase_dup l) end)
  (λ nainl : a ∉ l,
    have r   : nodup (erase_dup l), from nodup_erase_dup l,
    have nin : a ∉ erase_dup l, from
      assume ab : a ∈ erase_dup l, absurd (mem_of_mem_erase_dup ab) nainl,
    begin rw [erase_dup_cons_of_not_mem nainl], exact (nodup_cons nin r) end)

theorem erase_dup_eq_of_nodup [decidable_eq α] : ∀ {l : list α}, nodup l → erase_dup l = l
| []     d := rfl
| (a::l) d :=
  have nainl : a ∉ l, from not_mem_of_nodup_cons d,
  have dl : nodup l,  from nodup_of_nodup_cons d,
  by rw [erase_dup_cons_of_not_mem nainl, erase_dup_eq_of_nodup dl]

attribute [instance]
def decidable_nodup [decidable_eq α] : ∀ (l : list α), decidable (nodup l)
| []     := is_true nodup_nil
| (a::l) :=
  if h : a ∈ l then
    is_false (not_nodup_cons_of_mem h)
  else
    match (decidable_nodup l) with
    | (is_true nd)  := is_true (nodup_cons h nd)
    | (is_false d)  := is_false (not_nodup_cons_of_not_nodup d)
    end

private def dgen (a : α) : ∀ l, nodup l → nodup (map (λ b : β, (a, b)) l)
| []     h := nodup_nil
| (x::l) h :=
      have dl   : nodup l,                         from nodup_of_nodup_cons h,
      have dm   : nodup (map (λ b : β, (a, b)) l), from dgen l dl,
      have nxin : x ∉ l,                           from not_mem_of_nodup_cons h,
      have npin : (a, x) ∉ map (λ b, (a, b)) l,    from
        assume pin, absurd (mem_of_mem_map_pair₁ pin) nxin,
      nodup_cons npin dm

theorem nodup_product : ∀ {l₁ : list α} {l₂ : list β}, nodup l₁ → nodup l₂ → nodup (product l₁ l₂)
| []      l₂ n₁ n₂ := nodup_nil
| (a::l₁) l₂ n₁ n₂ :=
  have nainl₁ : a ∉ l₁,                          from not_mem_of_nodup_cons n₁,
  have n₃    : nodup l₁,                         from nodup_of_nodup_cons n₁,
  have n₄    : nodup (product l₁ l₂),            from nodup_product n₃ n₂,
  have dm    : nodup (map (λ b : β, (a, b)) l₂), from dgen a l₂ n₂,
  have dsj   : disjoint (map (λ b : β, (a, b)) l₂) (product l₁ l₂), from
    λ p : α × β, match p with
         | (a₁, b₁) :=
            λ (i₁ : (a₁, b₁) ∈ map (λ b, (a, b)) l₂) (i₂ : (a₁, b₁) ∈ product l₁ l₂),
              have a₁inl₁ : a₁ ∈ l₁, from mem_of_mem_product_left i₂,
              have a₁ = a, from eq_of_mem_map_pair₁ i₁,
              have a ∈ l₁, begin rw ←this, assumption end,
              absurd this nainl₁
         end,
  nodup_append_of_nodup_of_nodup_of_disjoint dm n₄ dsj

theorem nodup_filter (p : α → Prop) [decidable_pred p] :
  ∀ {l : list α}, nodup l → nodup (filter p l)
| []     nd := nodup_nil
| (a::l) nd :=
  have   nainl : a ∉ l,              from not_mem_of_nodup_cons nd,
  have   ndl   : nodup l,            from nodup_of_nodup_cons nd,
  have ndf   : nodup (filter p l), from nodup_filter ndl,
  have nainf : a ∉ filter p l,     from
    assume ainf, absurd (mem_of_mem_filter ainf) nainl,
  by_cases
    (λ pa  : p a, begin rw [filter_cons_of_pos _ pa], exact (nodup_cons nainf ndf) end)
    (λ npa : ¬ p a, begin rw [filter_cons_of_neg _ npa], exact ndf end)

lemma dmap_nodup_of_dinj {p : α → Prop} [h : decidable_pred p] {f : Π a, p a → β} (pdi : dinj p f) :
    ∀ {l : list α}, nodup l → nodup (dmap p f l)
| []     := assume P, nodup.ndnil
| (a::l) := assume Pnodup,
            if pa : p a then
              begin
                rw [dmap_cons_of_pos pa],
                apply nodup_cons,
                apply (not_mem_dmap_of_dinj_of_not_mem pdi pa),
                exact not_mem_of_nodup_cons Pnodup,
                exact dmap_nodup_of_dinj (nodup_of_nodup_cons Pnodup)
              end
            else
              begin
                rw [dmap_cons_of_neg pa],
                exact dmap_nodup_of_dinj (nodup_of_nodup_cons Pnodup)
              end

theorem nodup_concat {a : α} {l : list α} (h : a ∉ l) (h' : nodup l) : nodup (concat l a) :=
begin
  revert h, induction l with b l ih,
  { intro h₀, apply nodup_singleton },
  intro h₀, rw [concat_cons], apply nodup_cons,
  { simp, intro h₁, apply h₀, simp, cases h₁ with h₂ h₂, simp [h₂],
    exact absurd h₂ (not_mem_of_nodup_cons h') },
  apply ih,
  { apply nodup_of_nodup_cons h' },
  intro h₁, apply h₀, exact mem_cons_of_mem _ h₁
end

theorem nodup_insert [decidable_eq α] {a : α} {l : list α} (h : nodup l) : nodup (insert a l) :=
if h' : a ∈ l then by simp [h', h]
else begin rw [insert_of_not_mem h'], apply nodup_concat, repeat {assumption} end

theorem nodup_upto : ∀ n, nodup (upto n)
| 0     := nodup_nil
| (n+1) :=
  have d : nodup (upto n), from nodup_upto n,
  have n : n ∉ upto n, from
    assume i : n ∈ upto n, absurd (lt_of_mem_upto i) (nat.lt_irrefl n),
  nodup_cons n d

theorem nodup_union_of_nodup_of_nodup [decidable_eq α] {l₁ l₂ : list α}
    (h₁ : nodup l₁) (h₂ : nodup l₂) :
  nodup (l₁ ∪ l₂) :=
begin
  induction l₂ with a l₂ ih generalizing l₁,
  { exact h₁ },
  simp,
  apply ih,
  { apply nodup_of_nodup_cons h₂ },
  apply nodup_insert h₁
end

theorem nodup_inter_of_nodup [decidable_eq α] : ∀ {l₁ : list α} (l₂), nodup l₁ → nodup (l₁ ∩ l₂)
| []      l₂ d := nodup_nil
| (a::l₁) l₂ d :=
  have d₁     : nodup l₁,        from nodup_of_nodup_cons d,
  have d₂     : nodup (l₁ ∩ l₂), from nodup_inter_of_nodup _ d₁,
  have nainl₁ : a ∉ l₁,          from not_mem_of_nodup_cons d,
  have naini  : a ∉ l₁ ∩ l₂,     from λ i, absurd (mem_of_mem_inter_left i) nainl₁,
  by_cases
    (λ ainl₂  : a ∈ l₂, begin rw [inter_cons_of_mem _ ainl₂], exact (nodup_cons naini d₂) end)
    (λ nainl₂ : a ∉ l₂, begin rw [inter_cons_of_not_mem _ nainl₂], exact d₂ end)

end nodup

end list
