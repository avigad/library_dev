/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Sorting for lists.
-/
import .perm

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
parameters {α : Type uu} [decidable_eq α]
parameters (r : α → α → Prop) [decidable_rel r]
local infix `≼` : 50 := r

/- insertion sort -/

section insertion_sort

def ordered_insert (a : α) : list α → list α
| []       := [a]
| (b :: l) := if a ≼ b then a :: (b :: l) else b :: ordered_insert l

def insertion_sort : list α → list α
| []       := []
| (b :: l) := ordered_insert b (insertion_sort l)

end insertion_sort

section correctness
open perm

-- TODO(Jeremy): I tried to add [decidable_eq α] here, but Lean complained
-- that _inst_1 was already declared

theorem count_ordered_insert_eq (b a : α) : ∀ l, count b (ordered_insert a l) = count b (a :: l)
| []       := by simp [ordered_insert.equations.eqn_1]
| (c :: l) := decidable.by_cases
                (suppose a ≼ c,
                  by rw [ordered_insert.equations.eqn_2, if_pos this])
                (suppose ¬ a ≼ c,
                  begin
                    rw [ordered_insert.equations.eqn_2, if_neg this],
                    simp [count_cons', count_ordered_insert_eq]
                  end)

theorem mem_ordered_insert (b a : α) (l : list α) : b ∈ ordered_insert a l ↔ b ∈ a :: l :=
by simp [mem_iff_count_pos, count_ordered_insert_eq]

theorem perm_insertion_sort : ∀ l, insertion_sort l ~ l
| []       := take a, rfl
| (b :: l) := take a,
              begin
                rw [insertion_sort.equations.eqn_2, count_ordered_insert_eq],
                simp [count_cons', perm_insertion_sort l a]
              end

theorem sorted_ordered_insert (totr : total r) (transr : transitive r) (a : α) :
  ∀ l, sorted r l → sorted r (ordered_insert a l)
| []       := assume h, sorted_singleton r a
| (b :: l) :=
  assume h,
  have sorted r l, from sorted_of_sorted_cons r h,
  have h₀ : ∀ c ∈ l, b ≼ c, from forall_mem_rel_of_sorted_cons r h,
  decidable.by_cases
   (suppose a ≼ b,
     begin
       rw [ordered_insert.equations.eqn_2, if_pos this],
       have ∀ c ∈ b :: l, a ≼ c, from
         take c, suppose c ∈ b :: l,
         or.elim (eq_or_mem_of_mem_cons this)
           (suppose c = b, this^.symm ▸ ‹a ≼ b›)
           (suppose c ∈ l, transr ‹a ≼ b› (h₀ _ this)),
       sorted_cons r h this
     end)
   (suppose ¬ a ≼ b,
     have b ≼ a, from or.resolve_left (totr a b) this,
     begin
       rw [ordered_insert.equations.eqn_2, if_neg ‹¬ a ≼ b›],
       have h₁ : sorted r (ordered_insert r a l), from sorted_ordered_insert l ‹sorted r l›,
       have h₂ : ∀ c ∈ ordered_insert r a l, b ≼ c, from
         take c,
         suppose c ∈ ordered_insert r a l,
         have c ∈ a  :: l, from (mem_ordered_insert r c a l)^.mp this,
         or.elim (eq_or_mem_of_mem_cons this)
           (suppose c = a, begin rw this, exact ‹b ≼ a› end)
           (suppose c ∈ l, h₀ c this),
       show sorted r (b :: ordered_insert r a l), from sorted_cons r h₁ h₂
     end)
end correctness

end sort

vm_eval insertion_sort (λ m n : ℕ, m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]

end list
