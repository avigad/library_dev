import utils
open expr decidable monad

definition lex {T} [decidable_eq T] (gt : T → T → bool) : list T → list T → bool
| (s::ss) (t::ts) := if s = t then lex ss ts else gt s t
| _ _ := ff

definition majo {T} (gt : T → T → bool) (s : T) : list T → bool
| [] := tt
| (t::ts) := gt s t && majo ts

meta_definition contained (var_name : name) : expr → bool
| (var _) := ff
| (sort _) := ff
| (const _ _) := ff
| (app a b) := contained var_name a || contained var_name b
| (lam _ _ d b) := contained var_name b
| (pi _ _ d b) := contained var_name b
| (elet _ t v b) := contained var_name v || contained var_name b
| (macro _ _ _) := ff
| (local_const uniq _ _ _) := to_bool (uniq = var_name)
| (meta n t) := to_bool (n = var_name)

meta_definition contained_list (var_name : name) : list expr → bool
| (e::es) := contained var_name e || contained_list var_name es
| [] := ff

meta_definition gamma (lpo : expr → expr → bool) (s t : expr) : bool :=
to_bool (get_app_fn s = get_app_fn t) &&
lex lpo (get_app_args s) (get_app_args t) &&
majo lpo s (get_app_args t)

meta_definition beta (prec_gt lpo : expr → expr → bool) (s t : expr) : bool :=
prec_gt (get_app_fn s) (get_app_fn t) &&
majo lpo s (get_app_args t)

meta_definition alpha (lpo : expr → expr → bool) : list expr → expr → bool
| [] _ := ff
| (s::ss) t := to_bool (s = t) || lpo s t || alpha lpo ss t

meta_definition lpo (prec_gt : expr → expr → bool) (s t : expr) : bool :=
alpha (lpo prec_gt) (get_app_args s) t ||
beta prec_gt (lpo prec_gt) s t ||
gamma (lpo prec_gt) s t

set_option new_elaborator true
meta_definition prec_gt_of_name_list (ns : list name) : expr → expr → bool :=
let nis := rb_map.of_list (list_zipwithindex ns) in
λs t, match (rb_map.find nis (local_uniq_name s), rb_map.find nis (local_uniq_name t)) with
| (some si, some ti) := to_bool (si > ti)
| _ := ff
end

/-
set_option new_elaborator false
open tactic
example (i : Type) (f : i → i) (c d x : i) : true := by do
ef ← get_local `f, ec ← get_local `c, ed ← get_local `d,
syms ← return [ef,ec,ed],
prec_gt ← return $ prec_gt_of_name_list (list.map local_uniq_name [ef, ec, ed]),
sequence' (do s1 ← syms, s2 ← syms, return (do
  s1_fmt ← pp s1, s2_fmt ← pp s2,
  trace (s1_fmt ++ to_fmt " > " ++ s2_fmt ++ to_fmt ": " ++ to_fmt (prec_gt s1 s2))
)),

exprs ← @mapM tactic _ _ _ to_expr [`(f c), `(f (f c)), `(f d), `(f x), `(f (f x))],
sequence' (do e1 ← exprs, e2 ← exprs, return (do
  e1_fmt ← pp e1, e2_fmt ← pp e2,
  trace (e1_fmt ++ to_fmt" > " ++ e2_fmt ++ to_fmt": " ++ to_fmt (lpo prec_gt e1 e2))
)),

mk_const ``true.intro >>= apply
-/
