/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
eliminate existential quantifiers on the left, and look for contradictions. They rely on ematching
and congruence closure to try to finish off a goal at the end.

The procedures *do* split on disjunctions and recreate the smt state for each terminal call, so
they are only meant to be used on small, straightforward problems.

(For more substantial automation, I will experiment with a procedure that does similar things but
says within a single smt state, uses e-matching to chain forward with new facts, and splits
only as a last resort.)

We provide the following tactics:

  finish  -- solves the goal or fails
  clarify -- makes as much progress as possible while not leaving more than one goal
  safe    -- splits freely, finishes off whatever subgoals it can, and leaves the rest

All can take a list of simplifier rules, typically definitions that should be expanded.
(The equations and identities should not refer to the local context.)

The variants ifinish, iclarify, and isafe restrict to intuitionistic logic. They do not work
well with the current heuristic instantiation method used by ematch, so they should be revisited
when the API changes.
-/
import ..tactic.simp_tactic ...logic.basic
open tactic expr

-- TODO(Jeremy): move these
theorem implies_and_iff (p q r : Prop) : (p → q ∧ r) ↔ (p → q) ∧ (p → r) :=
iff.intro (λ h, ⟨λ hp, (h hp).left, λ hp, (h hp).right⟩) (λ h hp, ⟨h.left hp, h.right hp⟩)

theorem curry_iff (p q r : Prop) : (p ∧ q → r) ↔ (p → q → r) :=
iff.intro (λ h hp hq, h ⟨hp, hq⟩) (λ h ⟨hp, hq⟩, h hp hq)

theorem iff_def (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) :=
⟨ λh, ⟨h.1, h.2⟩, λ ⟨h₁, h₂⟩, ⟨h₁, h₂⟩ ⟩

theorem {u} bexists_def {α : Type u} (p q : α → Prop) : (∃ x (h : p x), q x) ↔ ∃ x, p x ∧ q x :=
⟨λ ⟨x, px, qx⟩, ⟨x, px, qx⟩, λ ⟨x, px, qx⟩, ⟨x, px, qx⟩⟩

-- theorem {u} forall_def {α : Type u} (p q : α → Prop) : (∀ x (h : p x), q x) ↔ ∀ x, p x → q x :=
-- iff.refl _


namespace auto

/- Utilities -/

meta def whnf_reducible (e : expr) : tactic expr := whnf e reducible

-- stolen from interactive.lean
private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

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
   tgt ← target >>= whnf_reducible,
   if (¬ (is_false tgt)) then
     if cfg.classical then
       (mk_mapp ``classical.by_contradiction [some tgt]) >>= apply >> intro1 >> skip
     else
       (mk_mapp ``decidable.by_contradiction [some tgt, none] >>= apply >> intro1 >> skip) <|>
       applyc ``by_contradiction_trick >> intro1 >> intro1 >> skip
   else
     skip

/-
  Normalize hypotheses. Bring conjunctions to the outside (for splitting), bring universal quantifiers to the
  outside (for ematching). The classical normalizer eliminates a → b in favor of ¬ a ∨ b.

  TODO (Jeremy): using the simplifier this way is inefficient. In particular, negations should be
  eliminated from the top down. Use ext_simplify_core instead.
-/

def logic_eval_simps : list name :=
[ ``not_true, ``not_false,
   ``or_true, ``or_false, ``true_or, ``false_or,
   ``true_and, ``and_true, ``false_and, ``and_false,
   ``true_implies_iff, ``false_implies_iff, ``implies_true_iff, ``implies_false_iff]

-- note: with current normalization procedure, or distribs cause exponential blowup
def common_normalize_lemma_names : list name :=
logic_eval_simps ++
[``and_assoc, ``or_assoc,
  -- unfold bounded quantifiers
  ``bexists_def,
  -- negations
  ``not_or_iff,
  ``not_exists_iff_forall_not,
  -- bring out conjunctions
  ``or_implies_distrib,  -- ((a ∨ b) → c) ↔ ((a → c) ∧ (b → c))
  ``implies_and_iff,     -- (a → b ∧ c) ↔ (a → b) ∧ (a → c))
  -- ``or_distrib,
  -- ``or_distrib_right,
  ``forall_and_distrib,
  -- bring out universal quantifiers
  ``exists_implies_distrib,
  -- good for intuitionistic logic
  ``curry_iff]

def classical_normalize_lemma_names : list name :=
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

/-
  Eliminate existential quantifiers.
-/

-- eliminate an existential quantifier if there is one
meta def eelim : tactic unit :=
do ctx ← local_context,
   first $ ctx.for $ λ h,
     do t ← infer_type h >>= whnf_reducible,
        guard (is_app_of t ``Exists),
        to_expr ``(exists.elim %%h) >>= apply >> intros >> clear h

-- eliminate all existential quantifiers, fails if there aren't any
meta def eelims : tactic unit := eelim >> repeat eelim

/-
  Substitute if there is a hypothesis x = t or t = x.
-/

-- carries out a subst if there is one, fails otherwise
meta def do_subst : tactic unit :=
do ctx ← local_context,
   first $ ctx.for $ λ h,
     do t ← infer_type h >>= whnf_reducible,
        match t with
        | `(%%a = %%b) := subst h
        | _            := failed
        end

meta def do_substs : tactic unit := do_subst >> repeat do_subst

/-
  Split all conjunctions.
-/

-- Assumes pr is a proof of t. Adds the consequences of t to the context
-- and returns tt if anything nontrivial has been added.
meta def add_conjuncts : expr → expr → tactic bool :=
λ pr t,
let assert_consequences := λ e t, mcond (add_conjuncts e t) skip (assertv_fresh t e >> skip) in
do t' ← whnf_reducible t,
   match t' with
   | `(%%a ∧ %%b) :=
     do e₁ ← mk_app ``and.left [pr],
        assert_consequences e₁ a,
        e₂ ← mk_app ``and.right [pr],
        assert_consequences e₂ b,
        return tt
  | `(true) :=
     do return tt
  | _ := return ff
end

-- return tt if any progress is made
meta def split_hyp (h : expr) : tactic bool :=
do t ← infer_type h,
   mcond (add_conjuncts h t) (clear h >> return tt) (return ff)

-- return tt if any progress is made
meta def split_hyps_aux : list expr → tactic bool
| []        := return ff
| (h :: hs) := do b₁ ← split_hyp h,
                  b₂ ← split_hyps_aux hs,
                  return (b₁ || b₂)

-- fail if no progress is made
meta def split_hyps : tactic unit :=
do ctx ← local_context,
   mcond (split_hyps_aux ctx) skip failed

/-
  Use each hypothesis to simplify the others. For example, given a and a → b, we get b, and given
  a ∨ b ∨ c and ¬ b we get a ∨ c.

  TODO(Jeremy): use a version of simp_at_using_hs that takes simp lemmas
-/

meta def self_simplify_hyps_aux : tactic unit :=
do ctx ← local_context,
   extra_simps ← mmap mk_const logic_eval_simps,
   first $ ctx.for $ λ h,
     do t ← infer_type h,
        mcond (is_prop t) (simp_at_using_hs h extra_simps) failed

meta def self_simplify_hyps : tactic unit :=
self_simplify_hyps_aux >> repeat self_simplify_hyps_aux

/-
  Eagerly apply all the preprocessing rules.
-/

meta def preprocess_hyps (cfg : auto_config) : tactic unit :=
do repeat (intro1 >> skip),
   preprocess_goal cfg,
   normalize_hyps cfg,
   repeat (do_substs <|> split_hyps <|> eelim <|> self_simplify_hyps)

/-
  The terminal tactic, used to try to finish off goals:
  - Call the simplifier again.
  - Call the contradiction tactic.
  - Open an SMT state, and use ematching and congruence closure, with all the universal
    statements in the context.

  TODO(Jeremy): allow users to specify extra theorems for ematching?
-/

meta def mk_hinst_lemmas : list expr → smt_tactic hinst_lemmas
| [] := return hinst_lemmas.mk
| (h :: hs) := do his ← mk_hinst_lemmas hs,
                  t ← infer_type h,
                  match t with
                  | (pi _ _ _ _) :=
                    do t' ← infer_type t,
                       if t' = `(Prop) then
                          (do new_lemma ← hinst_lemma.mk h,
                             return (hinst_lemmas.add his new_lemma)) <|> return his
                       else return his
                  | _ := return his
                  end

meta def done (s : simp_lemmas) (cfg : auto_config := {}) : tactic unit :=
do /- if cfg^.use_simp then simp_all s else skip, -/
   contradiction <|>
   (solve1 $
     (do revert_all,
         using_smt
         (do smt_tactic.intros,
             ctx ← local_context,
             hs ← mk_hinst_lemmas ctx,
             smt_tactic.repeat (smt_tactic.ematch_using hs >> smt_tactic.try smt_tactic.close))))

/-
  Tactics that perform case splits.
-/

inductive case_option
| force        -- fail unless all goals are solved
| at_most_one  -- leave at most one goal
| accept       -- leave as many goals as necessary

private meta def case_cont (s : case_option) (cont : case_option → tactic unit) : tactic unit :=
do match s with
   | case_option.force := cont case_option.force >> cont case_option.force
   | case_option.at_most_one :=
       -- if the first one succeeds, commit to it, and try the second
       (mcond (cont case_option.force >> return tt) (cont case_option.at_most_one) skip) <|>
       -- otherwise, try the second
       (swap >> cont case_option.force >> cont case_option.at_most_one)
   | case_option.accept := focus [cont case_option.accept, cont case_option.accept]
   end

-- three possible outcomes:
--   finds something to case, the continuations succeed ==> returns tt
--   finds something to case, the continutations fail ==> fails
--   doesn't find anything to case ==> returns ff
meta def case_hyp (h : expr) (s : case_option) (cont : case_option → tactic unit) : tactic bool :=
do t ← infer_type h,
   match t with
   | `(%%a ∨ %%b) := cases h >> case_cont s cont >> return tt
   | _            := return ff
   end

meta def case_some_hyp_aux (s : case_option) (cont : case_option → tactic unit) :
  list expr → tactic bool
| []      := return ff
| (h::hs) := mcond (case_hyp h s cont) (return tt) (case_some_hyp_aux hs)

meta def case_some_hyp (s : case_option) (cont : case_option → tactic unit) : tactic bool :=
local_context >>= case_some_hyp_aux s cont

/-
  The main tactics.
-/

meta def safe_core (s : simp_lemmas) (cfg : auto_config) : case_option → tactic unit :=
λ co,
do if cfg^.use_simp then simp_all s else skip,
   preprocess_hyps cfg,
   done s cfg <|>
     (mcond (case_some_hyp co safe_core)
       skip
       (match co with
         | case_option.force       := done s cfg
         | case_option.at_most_one := try (done s cfg)
         | case_option.accept      := try (done s cfg)
         end))

meta def clarify (s : simp_lemmas) (cfg : auto_config := {}) : tactic unit := safe_core s cfg case_option.at_most_one
meta def safe (s : simp_lemmas) (cfg : auto_config := {}) : tactic unit := safe_core s cfg case_option.accept
meta def finish (s : simp_lemmas) (cfg : auto_config := {}) : tactic unit := safe_core s cfg case_option.force

meta def iclarify (s : simp_lemmas) (cfg : auto_config := {}) : tactic unit := clarify s {cfg with classical := false}
meta def isafe (s : simp_lemmas) (cfg : auto_config := {}) : tactic unit := safe s {cfg with classical := false}
meta def ifinish (s : simp_lemmas) (cfg : auto_config := {}) : tactic unit := finish s {cfg with classical := false}

end auto

open auto

namespace tactic
namespace interactive

open lean lean.parser interactive interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def clarify (hs : parse opt_qexpr_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set [] hs [],
   auto.clarify s cfg

meta def safe (hs : parse opt_qexpr_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set [] hs [],
   auto.safe s cfg

meta def finish (hs : parse opt_qexpr_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set [] hs [],
   auto.finish s cfg

meta def iclarify (hs : parse opt_qexpr_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set [] hs [],
   auto.iclarify s cfg

meta def isafe (hs : parse opt_qexpr_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set [] hs [],
   auto.isafe s cfg

meta def ifinish (hs : parse opt_qexpr_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set [] hs [],
   auto.ifinish s cfg

end interactive
end tactic
