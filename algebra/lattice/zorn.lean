/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Zorn's lemmas.

Ported from Isabelle/HOL (written by Jacques D. Fleuriot, Tobias Nipkow, and Christian Sternagel).
-/
import ...data.set
noncomputable theory

universes u
open set classical
local attribute [instance] decidable_inhabited
local attribute [instance] prop_decidable

namespace zorn

section chain
parameters {α : Type u} {r : α → α → Prop}
local infix ` ≺ `:50  := r

def chain (c : set α) := pairwise_on c (λx y, x ≺ y ∨ y ≺ x)

lemma chain_insert {c : set α} {a : α} (hc : chain c) (ha : ∀b∈c, b ≠ a → a ≺ b ∨ b ≺ a) :
  chain (insert a c) :=
forall_insert_of_forall
  (take x hx, forall_insert_of_forall (hc x hx) (take hneq, (ha x hx hneq).symm))
  (forall_insert_of_forall (take x hx hneq, ha x hx $ take h', hneq h'.symm) (take h, (h rfl).rec _))

def super_chain (c₁ c₂ : set α) := chain c₂ ∧ c₁ ⊂ c₂

def is_max_chain (c : set α) := chain c ∧ ¬ (∃c', super_chain c c')

def succ_chain (c : set α) :=
if h : ∃c', chain c ∧ super_chain c c' then some h else c

lemma succ_spec {c : set α} (h : ∃c', chain c ∧ super_chain c c') :
  super_chain c (succ_chain c) :=
let ⟨c', hc'⟩ := h in
have chain c ∧ super_chain c (some h),
  from @some_spec _ (λc', chain c ∧ super_chain c c') _,
by simp [succ_chain, dif_pos, h, this.right]

lemma chain_succ {c : set α} (hc : chain c) : chain (succ_chain c) :=
if h : ∃c', chain c ∧ super_chain c c' then
  (succ_spec h).left
else
  by simp [succ_chain, dif_neg, h]; exact hc

lemma super_of_not_max {c : set α} (hc₁ : chain c) (hc₂ : ¬ is_max_chain c) :
  super_chain c (succ_chain c) :=
begin
  simp [is_max_chain, not_and_iff, not_not_iff] at hc₂,
  have ∃c', super_chain c c', from hc₂.neg_resolve_left hc₁,
  let ⟨c', hc'⟩ := this in
  show super_chain c (succ_chain c),
    from succ_spec ⟨c', hc₁, hc'⟩
end

lemma succ_increasing {c : set α} : c ⊆ succ_chain c :=
if h : ∃c', chain c ∧ super_chain c c' then
  have super_chain c (succ_chain c), from succ_spec h,
  this.right.left
else by simp [succ_chain, dif_neg, h, subset.refl]

inductive chain_closure : set α → Prop
| succ : ∀{s}, chain_closure s → chain_closure (succ_chain s)
| union : ∀{s}, (∀a∈s, chain_closure a) → chain_closure (⋃₀ s)

lemma chain_closure_empty : chain_closure ∅ :=
have chain_closure (⋃₀ ∅),
  from chain_closure.union $ take a h, h.rec _,
by simp at this; assumption

lemma chain_closure_closure : chain_closure (⋃₀ {s | chain_closure s}) :=
chain_closure.union $ take s hs, hs

variables {c c₁ c₂ c₃ : set α}

private lemma chain_closure_succ_total_aux (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂)
  (h : ∀{c₃}, chain_closure c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ succ_chain c₃ ⊆ c₂) :
  c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁ :=
begin
  induction hc₁,
  case _root_.zorn.chain_closure.succ c₃ hc₃ ih {
    cases ih with ih ih,
    { note h := h hc₃ ih,
      cases h with h h,
      { exact (or.inr $ h ▸ subset.refl _) },
      { exact (or.inl h) } },
    { exact (or.inr $ subset.trans ih succ_increasing) } },
  case _root_.zorn.chain_closure.union s hs ih {
    exact (or_of_not_implies $ take hn, sUnion_subset $ take a ha,
      have a ⊆ c₂ ∨ succ_chain c₂ ⊆ a, from ih a ha,
      this.resolve_right $ take h, hn $ subset.trans h $ subset_sUnion_of_mem ha) }
end

private lemma chain_closure_succ_total (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) (h : c₁ ⊆ c₂) :
  c₂ = c₁ ∨ succ_chain c₁ ⊆ c₂ :=
begin
  induction hc₂ generalizing c₁ hc₁ h,
  case _root_.zorn.chain_closure.succ c₂ hc₂ ih {
    note h₁ : c₁ ⊆ c₂ ∨ @succ_chain α r c₂ ⊆ c₁ :=
      (chain_closure_succ_total_aux hc₁ hc₂ $ take c₁, ih),
    cases h₁ with h₁ h₁,
    { note h₂ := ih hc₁ h₁,
      cases h₂ with h₂ h₂,
      { exact (or.inr $ h₂ ▸ subset.refl _) },
      { exact (or.inr $ subset.trans h₂ succ_increasing) } },
    { exact (or.inl $ subset.antisymm h₁ h) } },
  case _root_.zorn.chain_closure.union s hs ih {
    apply or.imp (take h', subset.antisymm h' h) id,
    apply classical.by_contradiction,
    simp [not_or_iff, sUnion_subset_iff, not_forall_iff_exists_not, not_implies_iff_and_not],
    intro h, cases h with h₁ h₂, cases h₂ with c₃ h₂, cases h₂ with h₂ hc₃,
    note h := chain_closure_succ_total_aux hc₁ (hs c₃ hc₃) (take c₄, ih _ hc₃),
    cases h with h h,
    { note h' := ih c₃ hc₃ hc₁ h,
      cases h' with h' h',
      { exact (h₂ $ h' ▸ subset.refl _) },
      { exact (h₁ $ subset.trans h' $ subset_sUnion_of_mem hc₃) } },
    { exact (h₂ $ subset.trans succ_increasing h) } }
end

lemma chain_closure_total (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) : c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
have c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁,
  from chain_closure_succ_total_aux hc₁ hc₂ $ take c₃ hc₃, chain_closure_succ_total hc₃ hc₂,
or.imp_right (suppose succ_chain c₂ ⊆ c₁, subset.trans succ_increasing this) this

lemma chain_closure_succ_fixpoint (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂)
  (h_eq : succ_chain c₂ = c₂) : c₁ ⊆ c₂ :=
begin
  induction hc₁,
  case _root_.zorn.chain_closure.succ c₁ hc₁ h {
    exact or.elim (chain_closure_succ_total hc₁ hc₂ h)
      (take h, h ▸ h_eq.symm ▸ subset.refl c₂) id },
  case _root_.zorn.chain_closure.union s hs ih {
    exact (sUnion_subset $ take c₁ hc₁, ih c₁ hc₁) }
end

lemma chain_closure_succ_fixpoint_iff (hc : chain_closure c) :
  succ_chain c = c ↔ c = ⋃₀ {c | chain_closure c} :=
⟨take h, subset.antisymm
    (subset_sUnion_of_mem hc)
    (chain_closure_succ_fixpoint chain_closure_closure hc h),
  suppose c = ⋃₀{c : set α | chain_closure c},
  subset.antisymm
    (calc succ_chain c ⊆ ⋃₀{c : set α | chain_closure c} :
        subset_sUnion_of_mem $ chain_closure.succ hc
      ... = c : this.symm)
    succ_increasing⟩

lemma chain_chain_closure (hc : chain_closure c) : chain c :=
begin
  induction hc,
  case _root_.zorn.chain_closure.succ c hc h {
    exact chain_succ h },
  case _root_.zorn.chain_closure.union s hs h {
    note h : ∀c∈s, zorn.chain c := h,
    exact take c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq,
      have t₁ ⊆ t₂ ∨ t₂ ⊆ t₁, from chain_closure_total (hs _ ht₁) (hs _ ht₂),
      or.elim this
        (suppose t₁ ⊆ t₂, h t₂ ht₂ c₁ (this hc₁) c₂ hc₂ hneq)
        (suppose t₂ ⊆ t₁, h t₁ ht₁ c₁ hc₁ c₂ (this hc₂) hneq) }
end

def max_chain := (⋃₀ {c | chain_closure c})

/-- Hausdorff's maximality principle

There exists a maximal totally ordered subset of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
lemma max_chain_spec : is_max_chain max_chain :=
classical.by_contradiction $
suppose ¬ is_max_chain (⋃₀ {c | chain_closure c}),
have super_chain (⋃₀ {c | chain_closure c}) (succ_chain (⋃₀ {c | chain_closure c})),
  from super_of_not_max (chain_chain_closure chain_closure_closure) this,
let ⟨h₁, h₂, (h₃ : (⋃₀ {c | chain_closure c}) ≠ succ_chain (⋃₀ {c | chain_closure c}))⟩ := this in
have succ_chain (⋃₀ {c | chain_closure c}) = (⋃₀ {c | chain_closure c}),
  from (chain_closure_succ_fixpoint_iff chain_closure_closure).mpr rfl,
h₃ this.symm

/-- Zorn's lemma

If every chain has an upper bound, then there is a maximal element -/
lemma zorn (h : ∀c, chain c → ∃ub, ∀a∈c, a ≺ ub) (trans : ∀{a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃m, ∀a, m ≺ a → a ≺ m :=
have ∃ub, ∀a∈max_chain, a ≺ ub,
  from h _ $ max_chain_spec.left,
let ⟨ub, (hub : ∀a∈max_chain, a ≺ ub)⟩ := this in
⟨ub, take a ha,
  have chain (insert a max_chain),
    from chain_insert max_chain_spec.left $ take b hb _, or.inr $ trans (hub b hb) ha,
  have a ∈ max_chain, from
    classical.by_contradiction $ assume h : a ∉ max_chain,
    max_chain_spec.right $ ⟨insert a max_chain, this, ssubset_insert h⟩,
  hub a this⟩

end chain

lemma zorn_weak_order {α : Type u} [weak_order α]
  (h : ∀c:set α, @chain α (≤) c → ∃ub, ∀a∈c, a ≤ ub) : ∃m:α, ∀a, m ≤ a → a = m :=
let ⟨m, hm⟩ := @zorn α (≤) h (take a b c, le_trans) in
⟨m, take a ha, le_antisymm (hm a ha) ha⟩

end zorn
