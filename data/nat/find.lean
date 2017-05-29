/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

Choice function for decidable predicates on natural numbers.

This module provides the following two declarations:

find      {p : nat → Prop} [d : decidable_pred p] : (∃ x, p x) → nat
find_spec {p : nat → Prop} [d : decidable_pred p] (ex : ∃ x, p x) : p (find ex)
-/

namespace nat
section find_x
parameter {p : ℕ → Prop}

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k ≤ n, ¬p k

parameters [∀x, decidable (p x)] (H : ∃n, p n)

private def wf_lbp : well_founded lbp :=
⟨let ⟨n, pn⟩ := H in 
suffices ∀m k, n ≤ k + m → acc lbp k, from λa, this _ _ (nat.le_add_left _ _),
λm, nat.rec_on m
  (λk kn, ⟨_, λy r, match y, r with ._, ⟨rfl, a⟩ := absurd pn (a _ kn) end⟩)
  (λm IH k kn, ⟨_, λy r, match y, r with ._, ⟨rfl, a⟩ := IH _ (by rw nat.add_right_comm; exact kn) end⟩)⟩

protected def find_x : {n // p n} :=
@well_founded.fix _ (λk, (∀n < k, ¬p n) → {n // p n}) lbp wf_lbp
(λm IH al, if pm : p m then ⟨m, pm⟩ else
    have ∀ n ≤ m, ¬p n, from λn h, or.elim (lt_or_eq_of_le h) (al n) (λe, by rw e; exact pm), 
    IH _ ⟨rfl, this⟩ (λn h, this n $ nat.le_of_succ_le_succ h))
0 (λn h, absurd h (nat.not_lt_zero _))
end find_x

protected definition find {p : nat → Prop} [d : decidable_pred p] (ex : ∃ x, p x) : nat :=
(nat.find_x ex).1

protected theorem find_spec {p : nat → Prop} [d : decidable_pred p] (ex : ∃ x, p x) : p (nat.find ex) :=
(nat.find_x ex).2
end nat