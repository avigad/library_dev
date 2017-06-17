/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Parallel computation of a computable sequence of computations by
a diagonal enumeration.
The important theorems of this operation are proven as
terminates_parallel and exists_of_mem_parallel.
(This operation is nondeterministic in the sense that it does not
honor sequence equivalence (irrelevance of computation time).)
-/
import data.seq.wseq
universe u

namespace computation
open wseq
variables {α : Type u}

def parallel.aux2 : list (computation α) → α ⊕ list (computation α) :=
list.foldr (λc o, match o with
| sum.inl a  := sum.inl a
| sum.inr ls := rmap (λ c', c' :: ls) (destruct c)
end) (sum.inr [])

def parallel.aux1 : list (computation α) × wseq (computation α) →
  α ⊕ list (computation α) × wseq (computation α)
| (l, S) := rmap (λ l', match seq.destruct S with
  | none := (l', nil)
  | some (none, S') := (l', S')
  | some (some c, S') := (c::l', S')
  end) (parallel.aux2 l)

-- parallel computation of an infinite stream of computations,
-- taking the first result
def parallel (S : wseq (computation α)) : computation α :=
corec parallel.aux1 ([], S)

lemma terminates_parallel.aux : ∀ {l : list (computation α)} {S c},
  c ∈ l → terminates c → terminates (corec parallel.aux1 (l, S)) :=
begin
  have lem1 : ∀ l S, (∃ (a : α), parallel.aux2 l = sum.inl a) →
    terminates (corec parallel.aux1 (l, S)),
  { intros l S e, cases e with a e,
    have this : corec parallel.aux1 (l, S) = return a,
    { apply destruct_eq_ret, simp [parallel.aux1], rw e, simp [rmap] },
    rw this, apply_instance },
  intros l S c m T, revert l S,
  apply @terminates_rec_on _ _ c T _ _,
  { intros a l S m, apply lem1,
    revert m, induction l with c l IH; intro; simp at m, { contradiction },
    cases m with e m,
    { rw -e, simp [parallel.aux2],
      cases list.foldr parallel.aux2._match_1 (sum.inr list.nil) l with a' ls,
      exacts [⟨a', rfl⟩, ⟨a, rfl⟩] },
    { cases IH m with a' e,
      simp [parallel.aux2], simp [parallel.aux2] at e,
      rw e, exact ⟨a', rfl⟩ } },
  { intros s IH l S m,
    have H1 : ∀ l', parallel.aux2 l = sum.inr l' → s ∈ l',
    { revert m, induction l with c l IH';
      intros m l' e'; simp at m, { contradiction },
      cases m with e m; simp [parallel.aux2] at e',
      { rw -e at e',
        cases list.foldr parallel.aux2._match_1 (sum.inr list.nil) l with a' ls;
        injection e' with e', rw -e', simp },
      { ginduction list.foldr parallel.aux2._match_1 (sum.inr list.nil) l with e a' ls;
        rw e at e', { contradiction },
        have := IH' m _ e,
        simp [parallel.aux2] at e',
        cases destruct c; injection e',
        rw -h, simp [this] } },
    ginduction parallel.aux2 l with h a l',
    { exact lem1 _ _ ⟨a, h⟩ },
    { have H2 : corec parallel.aux1 (l, S) = think _,
      { apply destruct_eq_think,
        simp [parallel.aux1],
        rw h, simp [rmap] },
      rw H2, apply @computation.think_terminates _ _ _,
      have := H1 _ h,
      cases seq.destruct S,
      { simp [parallel.aux1], apply IH, exact this },
      { cases a with c S',
        cases c with c; simp [parallel.aux1]; apply IH; simp [this] } } }
end

theorem terminates_parallel (S : wseq (computation α))
   {c} (h : c ∈ S) [T : terminates c] : terminates (parallel S) :=
suffices ∀ n (l : list (computation α)) S c,
  c ∈ l ∨ some (some c) = seq.nth S n →
  terminates c → terminates (corec parallel.aux1 (l, S)),
from let ⟨n, h⟩ := h in this n [] S c (or.inr h) T,
begin
  intro n, induction n with n IH; intros l S c o T,
  { cases o, { exact terminates_parallel.aux a T },
    have H : seq.destruct S = some (some c, _),
    { unfold seq.destruct has_map.map, rw -a, simp [option_bind] },
    ginduction (parallel.aux2 l) with h a l';
    have C : corec parallel.aux1 (l, S) = _,
    { apply destruct_eq_ret, simp [parallel.aux1], rw [h], simp [rmap] },
    { rw C, apply_instance },
    { apply destruct_eq_think, simp [parallel.aux1], rw [h, H], simp [rmap] },
    { rw C, apply @computation.think_terminates _ _ _,
      apply terminates_parallel.aux _ T, simp } },
  { cases o, { exact terminates_parallel.aux a T },
    ginduction (parallel.aux2 l) with h a l';
    have C : corec parallel.aux1 (l, S) = _,
    { apply destruct_eq_ret, simp [parallel.aux1], rw [h], simp [rmap] },
    { rw C, apply_instance },
    { apply destruct_eq_think, simp [parallel.aux1], rw [h], simp [rmap] },
    { rw C, apply @computation.think_terminates _ _ _,
      have TT : ∀ l', terminates (corec parallel.aux1 (l', S.tail)),
      { intro, apply IH _ _ _ (or.inr _) T, rw a, cases S with f al, refl },
      ginduction seq.nth S 0 with e o,
      { have D : seq.destruct S = none,
        { dsimp [seq.destruct], rw e, refl },
        rw D, simp [parallel.aux1], have TT := TT l',
        rwa [seq.destruct_eq_nil D, seq.tail_nil] at TT },
      { have D : seq.destruct S = some (o, S.tail),
        { dsimp [seq.destruct], rw e, refl },
        rw D, cases o with c; simp [parallel.aux1, TT] } } }
end

theorem exists_of_mem_parallel (S : wseq (computation α))
   {a} (h : a ∈ parallel S) : ∃ c ∈ S, a ∈ c :=
suffices ∀ C, a ∈ C → ∀ (l : list (computation α)) S,
  corec parallel.aux1 (l, S) = C → ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c,
from let ⟨c, h1, h2⟩ := this _ h [] S rfl in ⟨c, h1.resolve_left id, h2⟩,
begin
  let F : list (computation α) → α ⊕ list (computation α) → Prop,
  { intros l a, cases a with a l',
    exact ∃ c ∈ l, a ∈ c,
    exact ∀ a', (∃ c ∈ l', a' ∈ c) → (∃ c ∈ l, a' ∈ c) },
  have lem1 : ∀ (l : list (computation α)), F l (parallel.aux2 l),
  { intro l, induction l with c l IH; simp [parallel.aux2],
    { intros a h, cases h with c h, cases h with hn,
      exact false.elim hn },
    { simp [parallel.aux2] at IH,
      cases list.foldr parallel.aux2._match_1 (sum.inr list.nil) l with a ls;
      simp [parallel.aux2],
      { cases IH with c' cl, cases cl with cl ac,
        refine ⟨c', or.inr cl, ac⟩ },
      { ginduction destruct c with h a c'; simp [rmap],
        { refine ⟨c, list.mem_cons_self _ _, _⟩,
          rw destruct_eq_ret h,
          apply ret_mem },
        { intros a' h, cases h with d h, cases h with dm ad,
          simp at dm, cases dm with e dl,
          { rw e at ad, refine ⟨c, list.mem_cons_self _ _, _⟩,
            rw destruct_eq_think h,
            exact think_mem ad },
          { cases IH a' ⟨d, dl, ad⟩ with d dm, cases dm with dm ad,
            exact ⟨d, or.inr dm, ad⟩ } } } } },
  intros C aC, refine mem_rec_on aC _ (λ C' IH, _);
  intros l S e; have e' := congr_arg destruct e; have := lem1 l;
  simp [parallel.aux1] at e'; cases parallel.aux2 l with a' l'; injection e',
  { rw h at this, cases this with c cl, cases cl with cl ac,
    exact ⟨c, or.inl cl, ac⟩ },
  { ginduction seq.destruct S with e a; rw e at h,
    { exact let ⟨d, o, ad⟩ := IH _ _ h,
        ⟨c, cl, ac⟩ := this a ⟨d, o.resolve_right (not_mem_nil _), ad⟩ in
      ⟨c, or.inl cl, ac⟩ },
    { cases a with o S', cases o with c; simp [parallel.aux1] at h;
      cases IH _ _ h with d dm; cases dm with o ad; cases o with dl dS',
      { exact let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩ in ⟨c, or.inl cl, ac⟩ },
      { refine ⟨d, or.inr _, ad⟩,
        rw seq.destruct_eq_cons e,
        exact seq.mem_cons_of_mem _ dS' },
      { simp at dl, cases dl with dc dl,
        { rw dc at ad, refine ⟨c, or.inr _, ad⟩,
          rw seq.destruct_eq_cons e,
          apply seq.mem_cons },
        { exact let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩ in ⟨c, or.inl cl, ac⟩ } },
      { refine ⟨d, or.inr _, ad⟩,
        rw seq.destruct_eq_cons e,
        exact seq.mem_cons_of_mem _ dS' } } }
end

theorem parallel_empty (S : wseq (computation α)) (h : S.head ~> none) :
parallel S = empty _ :=
eq_empty_of_not_terminates $ λ ⟨a, m⟩,
let ⟨c, cs, ac⟩ := exists_of_mem_parallel S m,
    ⟨n, nm⟩ := exists_nth_of_mem cs,
    ⟨c', h'⟩ := head_some_of_nth_some _ nm in by injection h h'

end computation