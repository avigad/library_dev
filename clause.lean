import init.meta.tactic utils
open expr list tactic monad decidable

structure cls :=
(num_quants : ℕ)
(num_lits : ℕ)
(prf : expr)
(type : expr)

namespace cls

private meta_definition tactic_format (c : cls) : tactic format := do
prf_fmt : format ← pp (prf c),
type_fmt ← pp (type c),
return $ prf_fmt ++ to_fmt " : " ++ type_fmt ++ to_fmt " (" ++
  to_fmt (num_quants c) ++ to_fmt " quants, " ++ to_fmt (num_lits c) ++ to_fmt " lits)"

attribute [instance]
meta_definition cls_has_to_tactic_format : has_to_tactic_format cls :=
has_to_tactic_format.mk tactic_format

definition num_binders (c : cls) := num_quants c + num_lits c

/- private -/ lemma clause_of_formula {p} : p → ¬p → false := λx y, y x

meta_definition of_proof (prf : expr) : tactic cls := do
prf' ← mk_mapp ``clause_of_formula [none, some prf],
type' ← infer_type prf',
return (mk 0 1 prf' type')

meta_definition inst (c : cls) (e : expr) : cls :=
(if num_quants c > 0
  then mk (num_quants c - 1) (num_lits c)
  else mk 0 (num_lits c - 1))
(app (prf c) e) (instantiate_var (binding_body (type c)) e)

meta_definition open_const (c : cls) : tactic (cls × expr) := do
n ← mk_fresh_name,
b ← return $ local_const n (binding_name (type c)) (binding_info (type c)) (binding_domain (type c)),
return (inst c b, b)

meta_definition open_meta (c : cls) : tactic (cls × expr) := do
b ← mk_meta_var (binding_domain (type c)),
return (inst c b, b)

set_option new_elaborator true
meta_definition close_const (c : cls) (e : expr) : cls :=
match e with
| local_const uniq pp info t :=
    let abst_type' := abstract_local (type c) (local_uniq_name e) in
    let type' := pi pp binder_info.default t (abstract_local (type c) uniq) in
    let prf' := lam pp binder_info.default t (abstract_local (prf c) uniq) in
    if num_quants c > 0 ∨ has_var abst_type' then
      mk (num_quants c + 1) (num_lits c) prf' type'
    else
      mk 0 (num_lits c + 1) prf' type'
| _ := mk 0 0 (mk_var 0) (mk_var 0)
end
set_option new_elaborator false

meta_definition open_constn (c : cls) : nat → tactic (cls × list expr)
| 0 := return (c, nil)
| (n+1) := do
  (c', b) ← open_const c,
  (c'', bs) ← open_constn c' n,
  return (c'', b::bs)

meta_definition open_metan (c : cls) : nat → tactic (cls × list expr)
| 0 := return (c, nil)
| (n+1) := do
  (c', b) ← open_meta c,
  (c'', bs) ← open_metan c' n,
  return (c'', b::bs)

meta_definition close_constn (c : cls) (bs : list expr) : cls :=
match bs with
| nil := c
| b::bs' := close_const (close_constn c bs') b
end

meta_definition inst_mvars (c : cls) : tactic cls := do
prf' ← instantiate_mvars (prf c),
type' ← instantiate_mvars (type c),
return $ cls.mk (cls.num_quants c) (cls.num_lits c) prf' type'

private meta_definition get_binder (e : expr) (i : nat) :=
if i = 0 then binding_domain e else get_binder (binding_body e) (i-1)

inductive lit
| pos : expr → lit
| neg : expr → lit

namespace lit

definition formula : lit → expr
| (pos f) := f
| (neg f) := f

definition is_neg : lit → bool
| (pos _) := ff
| (neg _) := tt

definition is_pos (l : lit) : bool := bool.bnot (is_neg l)

meta_definition to_formula : lit → tactic expr
| (pos f) := mk_mapp ``not [some f]
| (neg f) := return f

end lit

set_option new_elaborator true
meta_definition get_lit (c : cls) (i : nat) : lit :=
let bind := get_binder (type c) (num_quants c + i) in
if is_app_of bind ``not = tt ∧ get_app_num_args bind = 1 then
  lit.pos (app_arg bind)
else
  lit.neg bind
set_option new_elaborator false

meta_definition lits_where (c : cls) (p : lit → bool) : list nat :=
list.filter (λl, p (get_lit c l) = tt) (range (num_lits c))

meta_definition get_lits (c : cls) : list lit :=
map (get_lit c) (range (num_lits c))

meta_definition is_maximal (gt : expr → expr → bool) (c : cls) (i : nat) : bool :=
list_empty (filter (λj, gt (lit.formula $ get_lit c j) (lit.formula $ get_lit c i) = tt) (range $ num_lits c))

set_option new_elaborator true
meta_definition normalize (c : cls) : tactic cls := do
opened  ← open_constn c (num_quants c + num_lits c),
lconsts_in_types ← return $ contained_lconsts_list (list.map local_type opened.2),
quants' ← return $ filter (λlc, rb_map.contains lconsts_in_types (local_uniq_name lc) = tt) opened.2,
lits' ← return $ filter (λlc, rb_map.contains lconsts_in_types (local_uniq_name lc) = ff) opened.2,
@return tactic tactic_is_monad _ $ close_constn opened.1 (quants' ++ lits')

end cls

meta_definition unify_lit : cls.lit → cls.lit → tactic unit
| (cls.lit.pos a) (cls.lit.pos b) := unify a b
| (cls.lit.neg a) (cls.lit.neg b) := unify a b
| _ _ := fail "cannot unify literals"

-- FIXME: this is most definitely broken with meta-variables that were already in the goal
meta_definition sort_and_constify_metas (exprs_with_metas : list expr) : tactic (list expr) := do
inst_exprs ← @mapM tactic _ _ _ instantiate_mvars exprs_with_metas,
metas ← return $ inst_exprs >>= get_metas,
match list.filter (λm, has_meta_var (get_meta_type m) = ff) metas with
| [] := if list_empty metas = tt then return [] else forM' metas (λm, do trace (to_string m), t ← infer_type m, trace (to_string t)) >> fail "could not sort metas"
| ((meta n t) :: _) := do
  t' ← infer_type (meta n t),
  uniq ← mk_fresh_name,
  c ← return (local_const uniq uniq binder_info.default t'),
  unify c (meta n t),
  rest ← sort_and_constify_metas metas,
  return (rest ++ [c])
| _ := failed
end
