/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Insertion sort and merge sort.
-/
import .perm

-- TODO(Jeremy): move this

namespace nat

theorem add_pos_left {m : ℕ} (h : m > 0) (n : ℕ) : m + n > 0 :=
calc
  m + n > 0 + n : nat.add_lt_add_right h n
    ... = n     : nat.zero_add n
    ... ≥ 0     : zero_le n

theorem add_pos_right (m : ℕ) {n : ℕ} (h : n > 0) : m + n > 0 :=
begin rw add_comm, exact add_pos_left h m end

theorem add_pos_iff_pos_or_pos (m n : ℕ) : m + n > 0 ↔ m > 0 ∨ n > 0 :=
iff.intro
  begin
    intro h,
    cases m with m,
    {simp [zero_add] at h, exact or.inr h},
    exact or.inl (succ_pos _)
  end
  begin
    intro h, cases h with mpos npos,
    { apply add_pos_left mpos },
    apply add_pos_right _ npos
  end

lemma succ_le_succ_iff (m n : ℕ) : succ m ≤ succ n ↔ m ≤ n :=
⟨le_of_succ_le_succ, succ_le_succ⟩

lemma lt_succ_iff_le (m n : ℕ) : m < succ n ↔ m ≤ n :=
succ_le_succ_iff m n

end nat



namespace list

section sorted
universe variable uu
variables {α : Type uu} (r : α → α → Prop)

def sorted : list α → Prop
| []       := true
| (a :: l) := sorted l ∧ ∀ b ∈ l, r a b

theorem sorted_nil : sorted r nil := trivial

theorem sorted_singleton (a : α) : sorted r [a] :=
⟨sorted_nil r, λ b h, absurd h (not_mem_nil b)⟩

theorem sorted_of_sorted_cons {a : α} {l : list α} (h : sorted r (a :: l)) : sorted r l :=
h^.left

theorem forall_mem_rel_of_sorted_cons {a : α} {l : list α} (h : sorted r (a :: l)) :
  ∀ b ∈ l, r a b :=
h^.right

theorem sorted_cons {a : α} {l : list α} (h₁ : sorted r l) (h₂ : ∀ b ∈ l, r a b) :
  sorted r (a :: l) :=
⟨h₁, h₂⟩

end sorted

/-
  sorting procedures
-/

section sort
universe variable uu
parameters {α : Type uu} (r : α → α → Prop) [decidable_rel r]
local infix `≼` : 50 := r

/- insertion sort -/

section insertion_sort

def ordered_insert (a : α) : list α → list α
| []       := [a]
| (b :: l) := if a ≼ b then a :: (b :: l) else b :: ordered_insert l

--@[simp]
--theorem ordered_insert_nil (a : α) : ordered_insert a [] = [a] := rfl

--@[simp]
--theorem ordered_insert_cons (a b : α) (l : list α) :
--  ordered_insert a (b :: l) = if a ≼ b then a :: (b :: l) else b :: ordered_insert a l :=
--rfl


def insertion_sort : list α → list α
| []       := []
| (b :: l) := ordered_insert b (insertion_sort l)

--attribute [simp] insertion_sort.equations.eqn_1 insertion_sort.equations.eqn_2

section correctness
parameter [deceqα : decidable_eq α]
include deceqα
open perm

-- TODO(Jeremy): anonymous type class parameters don't work well

theorem count_ordered_insert_eq (b a : α) : ∀ l, count b (ordered_insert a l) = count b (a :: l)
| []       := by simp [ordered_insert]
| (c :: l) := if h : a ≼ c then begin unfold ordered_insert, simp [if_pos, h] end
              else by simp [ordered_insert, if_neg, h, count_cons', count_ordered_insert_eq]

theorem mem_ordered_insert_iff (b a : α) (l : list α) : b ∈ ordered_insert a l ↔ b ∈ a :: l :=
begin repeat {rw mem_iff_count_pos}, simp [count_ordered_insert_eq] end

theorem perm_insertion_sort : ∀ l : list α, insertion_sort l ~ l
| []       := perm.nil
| (b :: l) := perm_of_forall_count_eq (take a,
                by simp [insertion_sort, count_ordered_insert_eq, count_cons',
                         count_eq_count_of_perm (perm_insertion_sort l) a])

section total_and_transitive
variables (totr : total r) (transr : transitive r)
include totr transr

theorem sorted_ordered_insert (a : α) : ∀ l, sorted r l → sorted r (ordered_insert a l)
| []       := assume h, sorted_singleton r a
| (b :: l) :=
  assume h,
  have sorted r l, from sorted_of_sorted_cons r h,
  have h₀ : ∀ c ∈ l, b ≼ c, from forall_mem_rel_of_sorted_cons r h,
  if h' : a ≼ b then
    begin
      simp [ordered_insert, if_pos, h'],
      have ∀ c ∈ b :: l, a ≼ c, from
        take c, suppose c ∈ b :: l,
        or.elim (eq_or_mem_of_mem_cons this)
          (suppose c = b, this^.symm ▸ ‹a ≼ b›)
          (suppose c ∈ l, transr ‹a ≼ b› (h₀ _ this)),
      show sorted r (a :: b :: l), from sorted_cons r h this
   end
  else
    have b ≼ a, from or.resolve_left (totr a b) h',
    begin
      simp [ordered_insert, if_neg, ‹¬ a ≼ b›],
      have h₁ : sorted r (ordered_insert r a l), from sorted_ordered_insert l ‹sorted r l›,
      have h₂ : ∀ c ∈ ordered_insert r a l, b ≼ c, from
        take c,
        suppose c ∈ ordered_insert r a l,
        have c ∈ a  :: l, from (mem_ordered_insert_iff r c a l)^.mp this,
        or.elim (eq_or_mem_of_mem_cons this)
          (suppose c = a, begin rw this, exact ‹b ≼ a› end)
          (suppose c ∈ l, h₀ c this),
      show sorted r (b :: ordered_insert r a l), from sorted_cons r h₁ h₂
    end

theorem sorted_insert_sort : ∀ l, sorted r (insertion_sort l)
| []       := sorted_nil r
| (a :: l) := sorted_ordered_insert totr transr a _ (sorted_insert_sort l)

end total_and_transitive
end correctness
end insertion_sort

/- merge sort -/

section merge_sort

-- TODO(Jeremy): observation: if instead we write (a :: (split l).1, b :: (split l).2), the
-- equation compiler can't prove the third equation

def split : list α → list α × list α
| []            := ([], [])
| [a]           := ([a], [])
| (a :: b :: l) := match split l with
                   | (l₁, l₂) := (a :: l₁, b :: l₂)
                   end

-- TODO(Jeremy): the cases is needed because the internal split_match gets a pair

private theorem split_cons_cons_aux (a b : α) (l : list α) :
  split (a :: b :: l) = match split l with
                   | (l₁, l₂) := (a :: l₁, b :: l₂)
                   end := rfl

@[simp]
theorem split_cons_cons (a b : α) (l : list α) :
  split (a :: b :: l) = (a :: (split l).1, b :: (split l).2) :=
begin rw [split_cons_cons_aux], cases split l, reflexivity end

theorem length_split_fst_le : ∀ l : list α, length ((split l).1) ≤ length l
| []            := nat.le_refl 0
| [a]           := nat.le_refl 1
| (a :: b :: l) := begin
                     simp [split_cons_cons] without add_comm,
                     exact nat.succ_le_succ (nat.le_succ_of_le (length_split_fst_le l))
                   end

theorem length_split_snd_le : ∀ l : list α, length ((split l).2) ≤ length l
| []            := nat.le_refl 0
| [a]           := nat.zero_le 1
| (a :: b :: l) := begin
                     simp without add_comm,
                     transitivity,
                     { apply add_le_add_right (length_split_snd_le l) },
                     simp [nat.one_add, nat.le_succ]
                   end

theorem length_split_cons_cons_fst_lt (a b : α) (l : list α) :
  length (split (a :: b :: l)).1 < length (a :: b :: l) :=
begin
  simp without add_comm,
  exact add_lt_add_of_le_of_lt (length_split_fst_le l) (nat.le_refl _)
end

theorem length_split_cons_cons_snd_lt (a b : α) (l : list α) :
  length (split (a :: b :: l)).2 < length (a :: b :: l) :=
begin
  simp without add_comm,
  exact add_lt_add_of_le_of_lt (length_split_snd_le l) (nat.le_refl _)
end

-- Do the well-founded recursion by hand, until the function definition system supports it.

private def merge.F :
  Π p : list α × list α,
      (Π p₁ : list α × list α, length p₁.1 + length p₁.2 < length p.1 + length p.2 → list α) →
    list α
| ([], l)           f := l
| (a :: l, [])      f := a :: l
| (a :: l, b :: l') f := if a ≼ b then
                           a :: f (l, b :: l') begin simp without add_comm, apply nat.le_refl end
                         else
                           b :: f (a :: l, l') begin apply nat.le_refl end

def merge := well_founded.fix (inv_image.wf _ nat.lt_wf) merge.F

theorem merge.def (p : list α × list α) : merge p = merge.F p (λ p h, merge p) :=
well_founded.fix_eq (inv_image.wf _ nat.lt_wf) merge.F p

@[simp]
theorem merge.equations.eq_1 (l : list α) : merge ([], l) = l :=
begin rw merge.def, reflexivity end

@[simp]
theorem merge.equations.eq_2 (a : α) (l : list α) : merge (a :: l, []) = a :: l :=
begin rw merge.def, reflexivity end

@[simp]
theorem merge.equations.eq_3 (a b : α) (l l' : list α) :
  merge (a :: l, b :: l') = if a ≼ b then
                             a :: merge (l, b :: l')
                           else
                             b :: merge (a :: l, l') :=
begin rw merge.def, reflexivity end

private def merge_sort.F :
  Π l : list α, (Π l₁ : list α, length l₁ < length l → list α) → list α
| []            f := []
| [a]           f := [a]
| (a :: b :: l) f := let p  := split (a :: b :: l),
                         l₁ := f p.1 (length_split_cons_cons_fst_lt a b l),
                         l₂ := f p.2 (length_split_cons_cons_snd_lt a b l) in
                     merge (l₁, l₂)

def merge_sort := well_founded.fix (inv_image.wf _ nat.lt_wf) merge_sort.F

theorem merge_sort.def (l : list α) : merge_sort l = merge_sort.F l (λ l h, merge_sort l) :=
well_founded.fix_eq (inv_image.wf _ nat.lt_wf) merge_sort.F l

@[simp]
theorem merge_sort.equations.eq_1 : merge_sort [] = [] :=
begin rw merge_sort.def, reflexivity end

@[simp]
theorem merge_sort.equations.eq_2 (a : α) : merge_sort [a] = [a] :=
begin rw merge_sort.def, reflexivity end

@[simp]
theorem merge_sort.equations.eq_3 (a b : α) (l : list α) :
  merge_sort (a :: b :: l) = let p := split (a :: b :: l) in
                             merge (merge_sort p.1, merge_sort p.2) :=
begin rw merge_sort.def, reflexivity end

section correctness
parameter [deceqα : decidable_eq α]
include deceqα

theorem count_split (a : α) : ∀ l : list α, count a (split l).1 + count a (split l).2 = count a l
| []            := rfl
| [a]           := rfl
| (a :: b :: l) := begin simp [count_cons'], rw [-count_split l], simp end

private def count_merge.F (c : α) :
  Π p : list α × list α,
      (Π p₁ : list α × list α, length p₁.1 + length p₁.2 < length p.1 + length p.2 →
        count c (merge p₁) = count c p₁.1 + count c p₁.2) →
    count c (merge p) = count c p.1 + count c p.2
| ([], l)            f := by simp
| (a :: l, [])       f := by simp
| (a :: l, b :: l')  f := if h : a ≼ b then
                            begin
                              note hrec := f (l, b :: l') begin simp without add_comm, apply nat.le_refl end,
                              simp [if_pos, h, count_cons', hrec]
                            end
                          else
                            begin
                              note hrec := f (a :: l, l') begin apply nat.le_refl end,
                              simp [if_neg, h, count_cons', hrec]
                            end

theorem count_merge (c : α) :
  ∀ p : list α × list α, count c (merge p) = count c p.1 + count c p.2 :=
well_founded.fix (inv_image.wf _ nat.lt_wf) (count_merge.F c)

theorem mem_merge_iff (a : α) (p : list α × list α) : a ∈ merge p ↔ a ∈ p.1 ∨ a ∈ p.2 :=
begin repeat { rw mem_iff_count_pos }, simp [count_merge, nat.add_pos_iff_pos_or_pos] end

private def perm_merge_sort.F :
  Π l : list α, (Π l₁ : list α, length l₁ < length l → merge_sort l₁ ~ l₁) →
    merge_sort l ~ l
| []  f           := by simp; exact perm.refl _
| [a] f           := by simp; exact perm.refl _
| (a :: b :: l) f :=
  perm.perm_of_forall_count_eq
  begin
    intro c,
    pose hrec₁ := perm.count_eq_count_of_perm (f _ (length_split_cons_cons_fst_lt a b l)) c,
    pose hrec₂ := perm.count_eq_count_of_perm (f _ (length_split_cons_cons_snd_lt a b l)) c,
    simp at hrec₁,
    simp at hrec₂,
    simp [hrec₁, hrec₂, count_merge, count_split, count_cons']
  end

theorem perm_merge_sort : ∀ l : list α, merge_sort l ~ l :=
well_founded.fix (inv_image.wf _ nat.lt_wf) perm_merge_sort.F

section total_and_transitive
variables (totr : total r) (transr : transitive r)
include totr transr

private def sorted_merge.F :
  Π p : list α × list α,
      (Π p₁ : list α × list α, length p₁.1 + length p₁.2 < length p.1 + length p.2 →
        (sorted r p₁.1 → sorted r p₁.2 → sorted r (merge p₁))) →
    sorted r p.1 → sorted r p.2 → sorted r (merge p)
| ([], l)           f h₁ h₂ := begin simp, exact h₂ end
| (a :: l, [])      f h₁ h₂ := begin simp, exact h₁ end
| (a :: l, b :: l') f h₁ h₂ :=
  have sorted r l, from sorted_of_sorted_cons r h₁,
  have sorted r l', from sorted_of_sorted_cons r h₂,
  have h₁₀ : ∀ c ∈ l, a ≼ c, from forall_mem_rel_of_sorted_cons r h₁,
  have h₂₀ : ∀ c ∈ l', b ≼ c, from forall_mem_rel_of_sorted_cons r h₂,
  if h : a ≼ b then
    begin
      note hrec := f (l, b :: l') begin simp without add_comm, apply nat.le_refl end,
      simp [if_pos, h],
      have h₃ : sorted r (merge r (l, b :: l')), from hrec ‹sorted r l› h₂,
      have h₄ : ∀ c ∈ merge r (l, b :: l'), a ≼ c,
      begin
        intros c hc,
        rw mem_merge_iff at hc,
        exact or.elim hc
          (suppose c ∈ l, show a ≼ c, from h₁₀ c this)
          (suppose c ∈ b :: l',
            or.elim (eq_or_mem_of_mem_cons this)
              (suppose c = b, show a ≼ c, from this^.symm ▸ ‹a ≼ b›)
              (suppose c ∈ l', show a ≼ c, from transr ‹a ≼ b› (h₂₀ c this)))
      end,
      show sorted r (a :: merge r (l, b :: l')), from sorted_cons r h₃ h₄
    end
  else
    have h' : b ≼ a, from or.resolve_left (totr a b) h,
    begin
      note hrec := f (a :: l, l') begin apply nat.le_refl end,
      simp [if_neg, h],
      have h₃ : sorted r (merge r (a :: l, l')), from hrec h₁ ‹sorted r l'›,
      have h₄ : ∀ c ∈ merge r (a :: l, l'), b ≼ c,
      begin
        intros c hc,
        rw mem_merge_iff at hc,
        exact or.elim hc
          (suppose c ∈ a :: l,
            or.elim (eq_or_mem_of_mem_cons this)
              (suppose c = a, show b ≼ c, from this^.symm ▸ ‹b ≼ a›)
              (suppose c ∈ l, show b ≼ c, from transr ‹b ≼ a› (h₁₀ c this)))
          (suppose c ∈ l', show b ≼ c, from h₂₀ c this)
      end,
      show sorted r (b :: merge r (a :: l, l')), from sorted_cons r h₃ h₄
    end

theorem sorted_merge : Π {p : list α × list α},
  sorted r p.1 → sorted r p.2 → sorted r (merge p) :=
well_founded.fix (inv_image.wf _ nat.lt_wf) (sorted_merge.F totr transr)


private def sorted_merge_sort.F :
  Π l : list α, (Π l₁ : list α, length l₁ < length l → sorted r (merge_sort l₁)) →
    sorted r (merge_sort l)
| []            f := by simp; exact sorted_nil r
| [a]           f := by simp; exact sorted_singleton r a
| (a :: b :: l) f :=
  begin
    simp,
    apply sorted_merge r totr transr,
    -- this should be handled by the simplifier, i.e. cancel out +1 and rewrite _ < _ + 1 to _ <= _
    { apply f,
      show length (split l)^.fst + (1 + 0) < length l + (1 + 1),
        from add_lt_add_of_le_of_lt (length_split_fst_le l) (add_lt_add_of_le_of_lt (le_refl 1) zero_lt_one) },
    { apply f,
      show length (split l)^.snd + (1 + 0) < length l + (1 + 1),
        from add_lt_add_of_le_of_lt (length_split_snd_le l) (add_lt_add_of_le_of_lt (le_refl 1) zero_lt_one) }
  end

theorem sorted_merge_sort : ∀ l : list α, sorted r (merge_sort l) :=
well_founded.fix (inv_image.wf _ nat.lt_wf) (sorted_merge_sort.F totr transr)

end total_and_transitive
end correctness
end merge_sort
end sort

/- try them out! -/

--vm_eval insertion_sort (λ m n : ℕ, m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]

--vm_eval merge_sort     (λ m n : ℕ, m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]

end list
