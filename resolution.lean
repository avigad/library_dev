import init.meta.tactic
import clausifier
open expr tactic

meta_definition mk_resolvent : expr → nat → expr → nat → tactic expr
| a 0 b 0 :=
  do ai ← clause_info_of_proof a,
  match ai with
  | clause_info.cons bnd lit rest := do
    t ← infer_type rest,
    if is_false t = ff then fail "non-false tail" else return (app b a)
  | clause_info.tail t := fail "resolution against tail"
  end
| a (m+1) b n :=
  do ai ← clause_info_of_proof a,
  match ai with
  | clause_info.cons bnd lit rest := do
    sub ← mk_resolvent rest m b n,
    return (lambda_local_const bnd sub)
  | _ := fail "not a cons"
  end
| a m b (n+1) :=
  do bi ← clause_info_of_proof b,
  match bi with
  | clause_info.cons bnd lit rest := do
    sub ← mk_resolvent a m rest n,
    return (lambda_local_const bnd sub)
  | _ := fail "not a cons"
  end

meta_definition resolve_idx (a : name) (ai : nat) (b : name) (bi : nat) (res : name) : tactic unit := do
ae ← get_local a,
be ← get_local b,
rese ← mk_resolvent ae ai be bi,
rest ← infer_type rese,
assertv res rest rese

example {a b} : (a → false) → (¬a → b) → b :=
λna nab, nab na

example {a b} : (¬a → false) → (a → b → false) → (b → false) :=
_

example {a b c} : (a → b) → (¬a → c) → (¬b → ¬c → false) :=
λab nac nb nc, absurd (λx, nb (ab x)) (λx, nc (nac x))

example {a b} : ¬(¬a ∨ b) ∨ (a → b) :=
by do clausify_target,
  resolve_idx `cls_3 0 `cls_1 1 `cls_4,
  resolve_idx `cls_4 0 `cls_2 0 `cls_5,
  assumption
