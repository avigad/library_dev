/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

List permutations.
-/
import .basic

namespace list
universe variable u
variables {α : Type u} [decidable_eq α]

def perm (s t : list α) : Prop :=
∀ a, count a s = count a t

theorem perm.def (s t : list α) : perm s t = ∀ a, count a s = count a t := rfl

namespace perm

infix ~ := perm

theorem refl (s : list α) : s ~ s := take a, rfl

theorem symm {s t : list α} (h : s ~ t) : t ~ s :=
take a, eq.symm (h a)

theorem trans {s t u : list α} (h₁ : s ~ t) (h₂ : t ~ u) : s ~ u :=
take a, eq.trans (h₁ a) (h₂ a)

theorem count_eq_count_of_perm (a : α) {s t : list α} (h : s ~ t) : count a s = count a t := h a

theorem eq_nil_of_perm_nil {s : list α} (h : s ~ nil) : s = nil :=
eq_nil_of_forall_not_mem
  (take a, not_mem_of_count_eq_zero
    begin rw [h a, count_nil] end)

theorem not_perm_nil_cons (a : α) (l : list α) : ¬ nil ~ (a :: l) :=
assume h,
have count a nil = count a (a :: l), from h a,
begin simp at this, contradiction end

theorem mem_iff_mem_of_perm {a : α} {l₁ l₂ : list α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
begin rw [mem_iff_count_pos a l₁, mem_iff_count_pos a l₂, h a] end

theorem mem_of_mem_of_perm {a : α} {l₁ l₂ : list α} (h : l₁ ~ l₂) (h' : a ∈ l₁) : a ∈ l₂ :=
(mem_iff_mem_of_perm h)^.mp h'

end perm
end list
