import .simp_tactic
open tactic

universe u
variable {α : Type}

example (s t u : set ℕ) (h : s ⊆ t ∩ u) (h' : u ⊆ s) : u ⊆ s → true :=
begin
  dunfold_all subset inter,
--  trace_state,
  intro1, triv
end

example (s t u : set ℕ) (h : s ⊆ t ∩ u) (h' : u ⊆ s) : u ⊆ s → true :=
begin
  delta_all subset inter,
--  trace_state,
  intro1, triv
end

example (x y z : ℕ) (h'' : true) (h : 0 + y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp_all,
--  trace_state,
  rw [-h, -h']
end

example (x y z : ℕ) (h'' : true) (h : 0 + y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simph_all
end

def my_id (x : α) := x

def my_id_def (x : α) : my_id x = x := rfl

example (x y z : ℕ) (h'' : true) (h : 0 + my_id y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simph_all [my_id_def]
end

@[simp]
lemma mem_set_of {a : α} {p : α → Prop} : a ∈ {a | p a} = p a := rfl

-- TODO: write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl
theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl
theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} := rfl

theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
begin
  dsimp_all [subset_def, union_def],
  intros x h,
  cases h; back_chaining_using_hs
end

theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
begin
  dsimp_all [subset_def, inter_def],
  intros x h,
  split; back_chaining_using_hs
end
