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

/- In the main library, (simp_at h) replaces the local constant h by
   a new local constant with the same name. This variant returns the
   new expression, so that a tactic can continue to use it. -/

meta def simp_at' (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic expr :=
do when (expr.is_local_constant h = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← simp_lemmas.mk_default,
   S     ← S.append extra_lemmas,
   (new_htype, heq) ← simplify S htype cfg,
   newh ← assert' (expr.local_pp_name h) new_htype,
   mk_eq_mp heq h >>= exact,
   try $ clear h,
   return newh

meta def simp_at_using_hs' (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic expr :=
do hs ← collect_ctx_simps,
   simp_at' h (list.filter (≠ h) hs ++ extra_lemmas) cfg

meta def simph_at' (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic expr :=
simp_at_using_hs' h extra_lemmas cfg

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
   newh ← assert' (expr.local_pp_name h) new_htype,
   mk_eq_mp heq h >>= exact,
   try $ clear h,
   return newh


/- Modifications of tactics in the library -/

-- unchanged
private meta def is_equation : expr → bool
| (expr.pi n bi d b) := is_equation b
| e                  := match (expr.is_eq e) with (some a) := tt | none := ff end

-- fixes a bug and clears a hypothesis earlier, so we can reuse the name: see below
meta def simp_intro_aux' (cfg : simp_config) (updt : bool) : simp_lemmas → bool → list name → tactic simp_lemmas
| S tt     [] := try (simplify_goal S cfg) >> return S
| S use_ns ns := do
  t ← target,
  if t.is_napp_of `not 1 then
    intro1_aux use_ns ns >> simp_intro_aux' S use_ns ns.tail
  else if t.is_arrow then
    do {
      d ← return t.binding_domain,
      (new_d, h_d_eq_new_d) ← simplify S d cfg,
      h_d ← intro1_aux use_ns ns,
      h_new_d ← mk_eq_mp h_d_eq_new_d h_d,
      assertv_core h_d.local_pp_name new_d h_new_d,
      clear h_d, -- this was two lines later
      h_new   ← intro1,
      new_S ← if updt && is_equation new_d then S.add h_new else return S,
      simp_intro_aux' new_S use_ns ns.tail -- bug: this is ns in the library
    }
    <|>
    -- failed to simplify... we just introduce and continue
    (intro1_aux use_ns ns >> simp_intro_aux' S use_ns ns.tail)
  else if t.is_pi || t.is_let then
    intro1_aux use_ns ns >> simp_intro_aux' S use_ns ns.tail
  else do
    new_t ← whnf t reducible,
    if new_t.is_pi then change new_t >> simp_intro_aux' S use_ns ns
    else
      try (simplify_goal S cfg) >>
      mcond (expr.is_pi <$> target)
        (simp_intro_aux' S use_ns ns)
        (if use_ns ∧ ¬ns.empty then failed else return S)

meta def simp_intro_lst_using' (ns : list name) (s : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
step $ simp_intro_aux' cfg ff s tt ns

meta def simph_intro_lst_using' (ns : list name) (s : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
step $
do s ← collect_ctx_simps >>= s.append,
   simp_intro_aux' cfg tt s tt ns


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
   simp_intro_lst_using' ns s {}

-- simplify all the hypotheses and the goal, using preceding hypotheses along the way
meta def simph_all (s : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
do ctx ← local_context,
   let ns := ctx.map local_pp_name,
   revert_lst ctx,
   simp_intro_lst_using' ns s {}


/- Interactive tactics -/

namespace interactive
open lean lean.parser interactive interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

-- copied from library
private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

-- copied from library
private meta def report_invalid_simp_lemma {α : Type} (n : name): tactic α :=
fail ("invalid simplification lemma '" ++ to_string n ++ "' (use command 'set_option trace.simp_lemmas true' for more details)")

-- copied from library
private meta def simp_lemmas.resolve_and_add (s : simp_lemmas) (n : name) (ref : expr) : tactic simp_lemmas :=
do
  p ← resolve_name n,
  match p.to_raw_expr with
  | const n _           :=
    (do b ← is_valid_simp_lemma_cnst reducible n, guard b, save_const_type_info n ref, s.add_simp n)
    <|>
    (do eqns ← get_eqn_lemmas_for tt n, guard (eqns.length > 0), save_const_type_info n ref, add_simps s eqns)
    <|>
    report_invalid_simp_lemma n
  | _ :=
    (do e ← i_to_expr p, b ← is_valid_simp_lemma reducible e, guard b, try (save_type_info e ref), s.add e)
    <|>
    report_invalid_simp_lemma n
  end

-- copied from library
private meta def simp_lemmas.add_pexpr (s : simp_lemmas) (p : pexpr) : tactic simp_lemmas :=
let e := p.to_raw_expr in
match e with
| (const c [])          := simp_lemmas.resolve_and_add s c e
| (local_const c _ _ _) := simp_lemmas.resolve_and_add s c e
| _                     := do new_e ← i_to_expr p, s.add new_e
end

-- copied from library
private meta def simp_lemmas.append_pexprs : simp_lemmas → list pexpr → tactic simp_lemmas
| s []      := return s
| s (l::ls) := do new_s ← simp_lemmas.add_pexpr s l, simp_lemmas.append_pexprs new_s ls

-- copied from library
-- TODO(Jeremy): note this is not private, because it is used by auto
meta def mk_simp_set (attr_names : list name) (hs : list pexpr) (ex : list name) : tactic simp_lemmas :=
do s₀ ← join_user_simp_lemmas attr_names,
   s₁ ← simp_lemmas.append_pexprs s₀ hs,
   -- add equational lemmas, if any
   ex ← ex.mfor (λ n, list.cons n <$> get_eqn_lemmas_for tt n),
   return $ simp_lemmas.erase s₁ $ ex.join

-- copied from library
private meta def simp_goal (cfg : simp_config) : simp_lemmas → tactic unit
| s := do
   (new_target, Heq) ← target >>= simplify_core cfg s `eq,
   tactic.assert `Htarget new_target, swap,
   Ht ← get_local `Htarget,
   mk_eq_mpr Heq Ht >>= tactic.exact

-- copied from library
private meta def simp_hyp (cfg : simp_config) (s : simp_lemmas) (h_name : name) : tactic unit :=
do h     ← get_local h_name,
   htype ← infer_type h,
   (new_htype, eqpr) ← simplify_core cfg s `eq htype,
   tactic.assert (expr.local_pp_name h) new_htype,
   mk_eq_mp eqpr h >>= tactic.exact,
   try $ tactic.clear h

-- copied from library
private meta def simp_hyps (cfg : simp_config) : simp_lemmas → list name → tactic unit
| s []      := skip
| s (h::hs) := simp_hyp cfg s h >> simp_hyps s hs

-- copied from library
private meta def simp_core (cfg : simp_config) (ctx : list expr) (hs : list pexpr) (attr_names : list name) (ids : list name) (loc : list name) : tactic unit :=
do s ← mk_simp_set attr_names hs ids,
   s ← s.append ctx,
   match loc : _ → tactic unit with
   | [] := simp_goal cfg s
   | _  := simp_hyps cfg s loc
   end,
   try tactic.triv, try (tactic.reflexivity reducible)


/- The new tactics -/

/-- Unfolds definitions in all the hypotheses and the goal. -/
meta def dunfold_all (ids : parse ident*) : tactic unit :=
tactic.dunfold_all ids

/-- Expands definitions in all the hypotheses and the goal. -/
meta def delta_all (ids : parse ident*) : tactic unit :=
tactic.dunfold_all ids

-- Note: in the next tactics we revert before building the simp set, because the
-- given lemmas should not mention the local context

/-- Applies dsimp to all the hypotheses and the goal. -/
meta def dsimp_all (es : parse opt_qexpr_list) (attr_names : parse with_ident_list)
  (ids : parse without_ident_list) : tactic unit :=
do n ← revert_all,
   s ← mk_simp_set attr_names es ids,
   dsimp_all_aux s n,
   dsimp_core s

/-- Simplifies all the hypotheses and the goal. -/
meta def simp_all (hs : parse opt_qexpr_list) (attr_names : parse with_ident_list)
  (ids : parse without_ident_list) (cfg : simp_config := {}) : tactic unit :=
do ctx ← local_context,
   let ns := ctx.map local_pp_name,
   revert_lst ctx,
   s     ← mk_simp_set attr_names hs ids,
   simp_intro_lst_using' ns s cfg,
   try tactic.triv, try (tactic.reflexivity reducible)

/-- Simplifies all the hypotheses and the goal, using preceding hypotheses along the way. -/
meta def simph_all (hs : parse opt_qexpr_list)  (attr_names : parse with_ident_list)
  (ids : parse without_ident_list) (cfg : simp_config := {}) : tactic unit :=
do ctx ← local_context,
   let ns := ctx.map local_pp_name,
   revert_lst ctx,
   s     ← mk_simp_set attr_names hs ids,
   simph_intro_lst_using' ns s cfg,
   try tactic.triv, try (tactic.reflexivity reducible)

end interactive
end tactic
