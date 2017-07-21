/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.
-/
import tools.converter.old_conv

namespace old_conv
meta def save_info (p : pos) : old_conv unit :=
λ r lhs, do
  ts ← tactic.read,
  -- TODO(Leo): include context
  tactic.save_info_thunk p (λ _, ts.format_expr lhs) >>
  return ⟨(), lhs, none⟩

meta def step {α : Type} (c : old_conv α) : old_conv unit :=
c >> return ()

meta def istep {α : Type} (line0 col0 line col : nat) (c : old_conv α) : old_conv unit :=
λ r lhs ts, (@scope_trace _ line col (λ _, (c >> return ()) r lhs ts)).clamp_pos line0 line col

meta def execute (c : old_conv unit) : tactic unit :=
conversion c

namespace interactive
open lean.parser
open interactive
open interactive.types

meta def itactic : Type :=
old_conv unit

meta def whnf : old_conv unit :=
old_conv.whnf

meta def dsimp : old_conv unit :=
old_conv.dsimp

meta def trace_state : old_conv unit :=
old_conv.trace_lhs

meta def change (p : parse texpr) : old_conv unit :=
old_conv.change p

meta def find (p : parse lean.parser.pexpr) (c : itactic) : old_conv unit :=
λ r lhs, do
  pat ← tactic.pexpr_to_pattern p,
  s   ← simp_lemmas.mk_default, -- to be able to use congruence lemmas @[congr]
  (found, new_lhs, pr) ←
     tactic.ext_simplify_core ff {zeta := ff, beta := ff, single_pass := tt, eta := ff, proj := ff} s
       (λ u, return u)
       (λ found s r p e, do
         guard (not found),
         matched ← (tactic.match_pattern_core reducible pat e >> return tt) <|> return ff,
         guard matched,
         ⟨u, new_e, pr⟩ ← c r e,
         return (tt, new_e, pr, ff))
       (λ a s r p e, tactic.failed)
       r lhs,
  if not found then tactic.fail "find converter failed, pattern was not found"
  else return ⟨(), new_lhs, some pr⟩

end interactive
end old_conv

namespace tactic
namespace interactive
open lean.parser
open interactive
open interactive.types

meta def old_conv (c : old_conv.interactive.itactic) : tactic unit :=
do t ← target,
   (new_t, pr) ← c.to_tactic `eq t,
   replace_target new_t pr

meta def find (p : parse lean.parser.pexpr) (c : old_conv.interactive.itactic) : tactic unit :=
old_conv $ old_conv.interactive.find p c

end interactive
end tactic
