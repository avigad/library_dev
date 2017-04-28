/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
eliminate existential quantifiers on the left, look for contradictions. They rely on ematching and
congruence closure to try to finish off a goal at the end.

The procedures *do* split on disjunctions and recreate the smt state for each terminal call, so
they are meant to be used on small, straightforward problems.

(For more substantial automation, I will experiment with a procedure that similar things but
says within a single smt state, uses e-matching to chain forward with new facts, and splits
only as a last resort.)

We provide the following tactics:

  finish  -- solves the goal or fails
  clarify -- makes as much progress as possible while not leaving more than one goal
  safe    -- splits freely, finishes off whatever subgoals it can, and leaves the rest

All can take a list of simplifier rules, typically definitions that should be expanded.
(The equations and identities should not refer to the local context.)

The variants ifinish, iclarify, and isafe restrict to intuitionistic logic.
-/
import ..tactic.simp_tactic ...logic.basic
open tactic expr

-- TODO(Jeremy): move these
theorem implies_and_iff (p q r : Prop) : (p → q ∧ r) ↔ (p → q) ∧ (p → r) :=
iff.intro (λ h, ⟨λ hp, (h hp).left, λ hp, (h hp).right⟩) (λ h hp, ⟨h.left hp, h.right hp⟩)

theorem curry_iff (p q r : Prop) : (p ∧ q → r) ↔ (p → q → r) :=
iff.intro (λ h hp hq, h ⟨hp, hq⟩) (λ h ⟨hp, hq⟩, h hp hq)

namespace auto

/-
  Configuration information for the auto tactics.
-/

structure auto_config : Type :=
(use_simp := tt)        -- call the simplifier
(classical := tt)       -- use classical logic

/-
  Preprocess goal.

  We want to move everything to the left of the sequent arrow. For intuitionistic logic,
  we replace the goal p with ∀ f, (p → f) → f and introduce.
-/

theorem by_contradiction_trick (p : Prop) (h : ∀ f : Prop, (p → f) → f) : p :=
h p id

meta def preprocess_goal (cfg : auto_config) : tactic unit :=
do repeat (intro1 >> skip),
   tgt ← target >>= whnf,
   if (¬ (is_false tgt)) then
     if cfg.classical then
       (mk_mapp ``classical.by_contradiction [some tgt]) >>= apply >> intro1 >> skip
     else
       (mk_mapp ``decidable.by_contradiction [some tgt, none] >>= apply >> intro1 >> skip) <|>
       applyc ``by_contradiction_trick >> intro1 >> intro1 >> skip
   else
     skip

/-
  Normalize hypotheses. Bring conjunctions to the outside (for splitting),
  bring universal quantifiers to the outside (for ematching).

  The classical normalizer eliminates a → b in favor of ¬ a ∨ b, but maybe this is not so important.

  TODO (Jeremy): using the simplifier this way is inefficient; use ext_simplify_core instead.
-/

-- stolen from interactive.lean
private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

meta def common_normalize_lemma_names : list name :=
[``and_assoc, ``or_assoc,
  -- negations
  ``not_or_iff,
  ``not_exists_iff_forall_not,
  -- bring out conjunctions
  ``or_implies_distrib,  -- ((a ∨ b) → c) ↔ ((a → c) ∧ (b → c))
  ``implies_and_iff,     -- (a → b ∧ c) ↔ (a → b) ∧ (a → c))
  ``or_distrib,
  ``or_distrib_right,
  ``forall_and_distrib,
  -- bring out universal quantifiers
  ``exists_implies_distrib,
  -- good for intuitionistic logic
  ``curry_iff
]

meta def classical_normalize_lemma_names : list name :=
common_normalize_lemma_names ++
[ -- negations
  ``classical.not_not_iff,
  ``classical.not_and_iff,
  ``classical.not_forall_iff_exists_not,
  -- implication
  ``classical.implies_iff_not_or]

meta def normalize_hyp (simps : simp_lemmas) (h : expr) : tactic expr :=
do htype ← infer_type h,
   mcond (is_prop htype)
     ((do (new_htype, heq) ← simplify simps htype,
           newh ← assert' (expr.local_pp_name h) new_htype,
           mk_eq_mp heq h >>= exact,
           try $ clear h,
           return newh) <|> return h)
     (return h)

meta def normalize_hyps (cfg : auto_config) : tactic unit :=
do simps ← if cfg.classical then
             add_simps simp_lemmas.mk classical_normalize_lemma_names
           else
             add_simps simp_lemmas.mk common_normalize_lemma_names,
   local_context >>= monad.mapm' (normalize_hyp simps)

-- for testing
section
  variables a b c d : Prop
  variables (p q : ℕ → Prop) (r : ℕ → ℕ → Prop)

  example (h₁ : ¬ (a → b ∨ c)) (h₂ : ¬ (b ∨ ¬ c)) : true :=
  begin
    normalize_hyps {classical := false},
    triv
  end

  example (h : ¬ ∀ x, (∃ y, r x y) → p x) : true :=
  begin
    normalize_hyps {},
    triv
  end
end

/- exists elims -/

-- eliminate an existential quantifier if there is one
meta def eelim : tactic unit :=
do ctx ← local_context,
   first $ ctx.for $ λ h,
     do t ← infer_type h >>= whnf,
        guard (is_app_of t ``Exists),
        to_expr ``(exists.elim %%h) >>= apply >> intros >> clear h

-- eliminate all existential quantifiers, fails if there aren't any
meta def eelims : tactic unit := eelim >> repeat eelim

/- subst -/

-- carries out a subst if there is one, fails otherwise
meta def do_subst : tactic unit :=
do ctx ← local_context,
   first $ ctx.for $ λ h,
     do t ← infer_type h >>= whnf,
        match t with
        | ```(%%a = %%b) := subst h
        | _              := failed
        end

meta def do_substs : tactic unit := do_subst >> repeat do_subst

-- Assumes pr is a proof of t. Adds the consequences of t to the context
-- and returns tt if anything nontrivial has been added.
meta def add_conjuncts (cfg : auto_config) : expr → expr → tactic bool :=
λ pr t,
let assert_consequences := λ e t, mcond (add_conjuncts e t) skip (assertv_fresh t e >> skip) in
do t' ← whnf t,
   match t' with
   | ```(%%a ∧ %%b) :=
     do e₁ ← mk_app ``and.left [pr],
        assert_consequences e₁ a,
        e₂ ← mk_app ``and.right [pr],
        assert_consequences e₂ b,
        return tt
  | _ := return ff
end

-- return tt if any progress is made
meta def split_hyp (cfg : auto_config) (h : expr) : tactic bool :=
do t ← infer_type h,
   mcond (add_conjuncts cfg h t) (clear h >> return tt) (return ff)

-- return tt if any progress is made
meta def split_hyps_aux (cfg :auto_config) : list expr → tactic bool
| []        := return ff
| (h :: hs) := do b₁ ← split_hyp cfg h,
                  b₂ ← split_hyps_aux hs,
                  return (b₁ || b₂)

-- fail if no progress is made
meta def split_hyps (cfg : auto_config) : tactic unit :=
do ctx ← local_context,
   mcond (split_hyps_aux cfg ctx) skip failed

/- safe forward reasoning:

   h : a → b ==> h : b     if we have a
   h : a → b ==> h : ¬ a   if we can refute b
   h : a ∨ b ==> h : b,    if we can refute a
   h : a ∨ b ==> h : a,    if we can refute b

   -- TODO: be more agressive about trying to prove / refute the side conditions?
-/

-- given t and ctx, produces a proof of ¬ t or fails
meta def refute (t : expr) (ctx : list expr) : tactic expr :=
do (find_same_type ```(¬ %%t) ctx) <|>
   (match t with
     | ```(¬ %%t') :=
       do h' ← find_same_type t' ctx,
          mk_app ``not_not_intro [t', h']
     | _ := failed
     end)

meta def chain_forward_using_hyp (h : expr) : tactic unit :=
do t ← infer_type h >>= whnf,
   ctx ← local_context,
   match t with
   | ```(%%a → %%b) :=
     (do h' ← find_same_type a ctx,
         assertv_fresh (h h') b,
         clear h) <|>
     do h' ← refute b ctx,
        e ← mk_app ``contrapos [a, b, h, h'],
        assertv_fresh e ```(¬ %%a),
        clear h
   | ```(%%a ∨ %%b) :=
     (do h' ← refute a ctx,
         e ← mk_app ``or.resolve_left [a, b, h, h'],
         assertv_fresh e b,
         clear h) <|>
     do h' ← refute a ctx,
        e ← mk_app ``or.resolve_right [a, b, h, h'],
        assertv_fresh e a,
        clear h
   | _ := failed
   end

meta def apply_nonsplitting_rules (cfg : auto_config) : tactic unit :=
do repeat (intro1 >> skip),
   preprocess_goal cfg,
   normalize_hyps cfg,
   try do_substs,
   repeat (split_hyps cfg <|> eelim <|>
     do ctx ← local_context,
        first $ ctx^.for chain_forward_using_hyp)

/- terminal tactic -/

private meta def simp_all_default := simp_lemmas.mk_default >>= simp_all

meta def mk_hinst_lemmas : list expr → smt_tactic hinst_lemmas
| [] := return hinst_lemmas.mk
| (h :: hs) := do his ← mk_hinst_lemmas hs,
                  t ← infer_type h,
                  match t with
                  | (pi _ _ _ _) :=
                    do t' ← infer_type t,
                       if t' = ```(Prop) then
                          (do new_lemma ← hinst_lemma.mk h,
                             return (hinst_lemmas.add his new_lemma)) <|> return his
                       else return his
                  | _ := return his
                  end

meta def done (cfg : auto_config := {}) : tactic unit :=
do if cfg^.use_simp then simp_all_default else skip,
   contradiction <|>
   (do revert_all,
       using_smt
         (do smt_tactic.intros,
             ctx ← local_context,
             hs ← mk_hinst_lemmas ctx,
--           smt_tactic.trace_state,
--           l ← smt_tactic.get_facts,
--           smt_tactic.trace l,
             smt_tactic.repeat (smt_tactic.ematch_using hs >> smt_tactic.try smt_tactic.close)))

/- tactics that introduce additional goals -/

inductive case_option
| force | at_most_one | accept

private meta def case_cont (s : case_option) (cont : case_option → tactic unit) : tactic unit :=
do match s with
   | case_option.force := cont case_option.force >> cont case_option.force
   | case_option.at_most_one := (cont case_option.force >> cont case_option.at_most_one) <|>
                                 (swap >> cont case_option.force >> cont case_option.at_most_one)
   | case_option.accept := focus [cont case_option.accept, cont case_option.accept]
   end

-- possible outcomes:
--   finds something to case, the continuations succeed ==> returns tt
--   finds something to case, the continutations fail ==> fails
--   doesn't find anything to case ==> returns ff

meta def case_hyp (h : expr) (s : case_option) (cont : case_option → tactic unit) : tactic bool :=
do t ← infer_type h,
   match t with
   | ```(%%a ∨ %%b) := cases h >> case_cont s cont >> return tt
   | _              := return ff
   end

meta def case_some_hyp_aux (s : case_option) (cont : case_option → tactic unit) : list expr → tactic bool
| []      := return ff
| (h::hs) := mcond (case_hyp h s cont) (return tt) (case_some_hyp_aux hs)

meta def case_some_hyp (s : case_option) (cont : case_option → tactic unit) : tactic bool :=
local_context >>= case_some_hyp_aux s cont

meta def safe_core (cfg : auto_config) : case_option → tactic unit :=
λ s,
do if cfg^.use_simp then simp_all_default else skip,
   apply_nonsplitting_rules cfg,
   done cfg <|>
     (mcond (case_some_hyp s safe_core)
       skip
       (match s with
         | case_option.force       := done cfg
         | case_option.at_most_one := try (done cfg)
         | case_option.accept      := try (done cfg)
         end))

meta def clarify (cfg : auto_config := {}) : tactic unit := safe_core cfg case_option.at_most_one
meta def safe (cfg : auto_config := {}) : tactic unit := safe_core cfg case_option.accept
meta def finish (cfg : auto_config := {}) : tactic unit := safe_core cfg case_option.force

meta def iclarify (cfg : auto_config := {}) : tactic unit := clarify { cfg with classical := false }
meta def isafe (cfg : auto_config := {}) : tactic unit := safe { cfg with classical := false }
meta def ifinish (cfg : auto_config := {}) : tactic unit := finish { cfg with classical := false }

end auto

open auto


/- main tactics -/

example (m n k : ℕ) (h : n = m) (h' : k = m) : n = k :=
by done

/- tests -/

section

variables a b c d : Prop

example : a ∧ b → a := by finish
example : a → (a → b) → (b → c) ∧ (d → ¬ c) → ¬ d := by finish

example : a ∨ b → b ∨ a := by finish {use_simp := false}

example : a ∨ b ∨ c → b ∨ a :=
begin
  safe, -- TODO: get the forward chaining result.
  admit
end

example : ¬ (a ↔ ¬ a) :=
begin
  finish
end

example : a ∨ b ∨ c → b ∨ a :=
begin
  clarify,
  admit
end

example : a ∨ b ∨ c ∨ d → b ∨ a :=
begin
  safe,
  admit
end

end

section

variables (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop)
variables (P Q R : Prop)
variable  (g : bool → nat)

example (h₁ : ∀ x, p x → q x) (h₂ : ∀ x, p x) : q a :=
by finish

example (h₁ : p a) : ∃ x, p x :=
by finish

example (h₁ : p a) (h₂ : p b) (h₃ : q b) : ∃ x, p x ∧ q x :=
by finish

example (h : ∃ x, p x ∧ r x x) (h' : ∀ x, r x x → q x) : ∃ x, p x ∧ q x :=
by finish

example (h : ∃ x, q x ∧ p x)  : ∃ x, p x ∧ q x :=
by finish

example (h₁ : ∀ x, q x → p x) (h₃ : q a)  : ∃ x, p x :=
by finish

example (h₁ : ∀ x, p x → q x → false) (h₂ : p a) (h₃ : p b) (h₄ : q b) : false :=
by finish

example (h : ∀ x, p x) (h₁ : ∀ x, p x → q x) : ∀ x, q x :=
by finish

example (h : ∃ x, p x) (h₁ : ∀ x, p x → q x) : ∃ x, q x :=
by finish

example (f : Prop) (h : p a) (h₁ : ∀ x, p x → q x) (h₂ : ∀ x, q x → f) : f :=
begin [smt]
  note h₃ := h₁ _ h,    -- curiously: this is needed
  ematch_using [h, h₁, h₂]
end

example (f : Prop) (h : p a) (h₁ : ∀ x, ¬ p x ∨ q x) (h₂ : ∀ x, ¬ q x ∨ f) : f :=
begin [smt]
  ematch_using [h, h₁, h₂],
  smt_tactic.get_facts >>= smt_tactic.trace,
  ematch_using [h, h₁, h₂],
end

example (h : ¬ ∀ x, ¬ p x) (h₁ : ∀ x, p x → q x) (h₂ : ∀ x, ¬ q x) : false :=
by finish

example (h : p a) (h' : p a → false) : false :=
by finish

end
