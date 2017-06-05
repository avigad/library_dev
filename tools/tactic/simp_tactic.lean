/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Variants of the simplifier tactics.
-/
import init.meta.lean.parser
import .tactic
open expr

namespace tactic

/- The simp tactics use default simp rules. This version uses only the given list. -/

meta def simp_only (hs : list expr) (cfg : simp_config := {}) : tactic unit :=
do S ← simp_lemmas.mk^.append hs,
   simplify_goal S cfg >> try triv

meta def simp_only_at (h : expr) (hs : list expr := []) (cfg : simp_config := {}) :
  tactic expr :=
do when (expr.is_local_constant h = ff)
     (fail "tactic simp_only_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← simp_lemmas.mk^.append hs,
   (new_htype, heq) ← simplify S htype cfg,
   newh ← assert (expr.local_pp_name h) new_htype,
   mk_eq_mp heq h >>= exact,
   try $ clear h,
   return newh

/- Tactics that apply to all hypothesis and the goal. These duplicate some code
   from simp_tactic. -/

private meta def dunfold_all_aux (cs : list name) : ℕ → tactic unit
| 0     := skip
| (k+1) := do (expr.pi n bi d b : expr) ← target,
                new_d ← dunfold_core reducible default_max_steps cs d,
                change $ expr.pi n bi new_d b,
                intro1,
                dunfold_all_aux k

-- unfold constants in all hypotheses and the goal
meta def dunfold_all (cs : list name) : tactic unit :=
do n ← revert_all,
   dunfold_all_aux cs n,
   dunfold cs

private meta def delta_all_aux (cs : list name) : ℕ → tactic unit
| 0     := skip
| (k+1) := do (expr.pi n bi d b : expr) ← target,
                new_d ← delta_core {} cs d,
                change $ expr.pi n bi new_d b,
                intro1,
                delta_all_aux k

-- expand definitions in all hypotheses and the goal
meta def delta_all (cs : list name) : tactic unit :=
do n ← revert_all,
   delta_all_aux cs n,
   delta cs

meta def dsimp_all_aux (s : simp_lemmas) : ℕ → tactic unit
| 0     := skip
| (k+1) := do expr.pi n bi d b ← target,
              h_simp ← s.dsimplify d,
              tactic.change $ expr.pi n bi h_simp b,
              intron 1,
              dsimp_all_aux k

-- apply dsimp at all the hypotheses and the goal
meta def dsimp_all (s : simp_lemmas) : tactic unit :=
do n ← revert_all,
   dsimp_all_aux s n,
   dsimp_core s

-- simplify all the hypotheses and the goal
meta def simp_all (s : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
do ctx ← local_context,
   let ns := ctx.map local_pp_name,
   revert_lst ctx,
   simp_intro_lst_using ns s {}

-- simplify all the hypotheses and the goal, using preceding hypotheses along the way
meta def simph_all (s : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
do ctx ← local_context,
   let ns := ctx.map local_pp_name,
   revert_lst ctx,
   simp_intro_lst_using ns s {}

end tactic
