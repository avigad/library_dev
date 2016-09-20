import init.meta.tactic utils
open expr list tactic monad decidable

structure cls :=
(num_quants : ℕ)
(num_lits : ℕ)
(has_fin : bool)
(prf : expr)
(type : expr)

namespace cls

private meta_definition tactic_format (c : cls) : tactic format := do
prf_fmt : format ← pp (prf c),
type_fmt ← pp (type c),
fin_fmt ← return $ to_fmt (if has_fin c = tt then ", has final" else ""),
return $ prf_fmt ++ to_fmt " : " ++ type_fmt ++ to_fmt " (" ++
  to_fmt (num_quants c) ++ to_fmt " quants, " ++ to_fmt (num_lits c) ++ to_fmt " lits" ++ fin_fmt ++ to_fmt ")"

attribute [instance]
meta_definition cls_has_to_tactic_format : has_to_tactic_format cls :=
has_to_tactic_format.mk tactic_format

definition num_binders (c : cls) : ℕ :=
if has_fin c = tt then num_quants c + num_lits c - 1
else num_quants c + num_lits c

meta_definition of_proof_and_type (prf type : expr) : cls :=
mk 0 1 tt prf type

meta_definition of_proof (prf : expr) : tactic cls := do
type ← infer_type prf,
return (of_proof_and_type prf type)

meta_definition inst (c : cls) (e : expr) : cls :=
(if num_quants c > 0
  then mk (num_quants c - 1) (num_lits c)
  else mk 0 (num_lits c - 1)) (has_fin c)
(app (prf c) e) (instantiate_var (binding_body (type c)) e)

meta_definition open_const (c : cls) : tactic (cls × expr) := do
n ← mk_fresh_name,
b ← return $ local_const n (binding_name (type c)) (binding_info (type c)) (binding_domain (type c)),
return (inst c b, b)

meta_definition open_meta (c : cls) : tactic (cls × expr) := do
b ← mk_meta_var (binding_domain (type c)),
return (inst c b, b)

meta_definition close_const (c : cls) (e : expr) : cls :=
match e with
| local_const uniq pp info t :=
    let abst_type' := abstract_local (type c) (local_uniq_name e) in
    let type' := pi pp binder_info.default t (abstract_local (type c) uniq) in
    let prf' := lam pp binder_info.default t (abstract_local (prf c) uniq) in
    if num_quants c > 0 ∨ has_var abst_type' then
      mk (num_quants c + 1) (num_lits c) (has_fin c) prf' type'
    else
      mk 0 (num_lits c + 1) (has_fin c) prf' type'
| _ := mk 0 0 (has_fin c) (mk_var 0) (mk_var 0)
end

meta_definition open_constn : cls → ℕ → tactic (cls × list expr)
| c 0 := return (c, nil)
| c (n+1) := do
  (c', b) ← open_const c,
  (c'', bs) ← open_constn c' n,
  return (c'', b::bs)

meta_definition open_metan : cls → ℕ → tactic (cls × list expr)
| c 0 := return (c, nil)
| c (n+1) := do
  (c', b) ← open_meta c,
  (c'', bs) ← open_metan c' n,
  return (c'', b::bs)

meta_definition close_constn : cls → list expr → cls
| c [] := c
| c (b::bs') := close_const (close_constn c bs') b

meta_definition inst_mvars (c : cls) : tactic cls := do
prf' ← instantiate_mvars (prf c),
type' ← instantiate_mvars (type c),
return $ mk (num_quants c) (num_lits c) (has_fin c) prf' type'

inductive lit
| left : expr → lit
| right : expr → lit
| final : expr → lit

namespace lit

definition formula : lit → expr
| (left f) := f
| (right f) := f
| (final f) := f

definition is_neg : lit → bool
| (left _) := tt
| (right _) := ff
| (final _) := ff

definition is_pos (l : lit) : bool := bool.bnot (is_neg l)

meta_definition to_formula (l : lit) : tactic expr :=
if is_neg l = tt then mk_mapp ``not [some (formula l)]
else return (formula l)

meta_definition type_str : lit → string
| (lit.left _) := "left"
| (lit.right _) := "right"
| (lit.final _) := "final"

end lit

attribute [instance]
meta_definition lit_has_to_tactic_format : has_to_tactic_format lit :=
has_to_tactic_format.mk (λl, do
pp_f ← pp (lit.formula l),
return $ to_fmt (lit.type_str l) ++ " (" ++ pp_f ++ ")")

private meta_definition get_binding_body : expr → ℕ → expr
| e 0 := e
| e (i+1) := get_binding_body (binding_body e) i

private meta_definition get_binder (e : expr) (i : nat) :=
binding_domain (get_binding_body e i)

meta_definition get_lit (c : cls) (i : nat) : lit :=
if has_fin c ∧ num_lits c = i + 1 then lit.final (get_binding_body (type c) (num_quants c + i))
else let bind := get_binder (type c) (num_quants c + i) in
if is_app_of bind ``not = tt ∧ get_app_num_args bind = 1 then
  lit.right (app_arg bind)
else
  lit.left bind

meta_definition lits_where (c : cls) (p : lit → bool) : list nat :=
list.filter (λl, p (get_lit c l) = tt) (range (num_lits c))

meta_definition get_lits (c : cls) : list lit :=
list.map (get_lit c) (range (num_lits c))

meta_definition is_maximal (gt : expr → expr → bool) (c : cls) (i : nat) : bool :=
list.empty (filter (λj, gt (lit.formula $ get_lit c j) (lit.formula $ get_lit c i) = tt) (range $ num_lits c))

meta_definition normalize (c : cls) : tactic cls := do
opened  ← open_constn c (num_binders c),
lconsts_in_types ← return $ contained_lconsts_list (list.map local_type opened.2),
quants' ← return $ filter (λlc, rb_map.contains lconsts_in_types (local_uniq_name lc) = tt) opened.2,
lits' ← return $ filter (λlc, rb_map.contains lconsts_in_types (local_uniq_name lc) = ff) opened.2,
@return tactic tactic_is_monad _ $ close_constn opened.1 (quants' ++ lits')

lemma fin_to_pos_helper {p} (Hp : p) : ¬p → false := take Hnp, Hnp Hp
meta_definition fin_to_pos (c : cls) : tactic cls := do
guard $ has_fin c,
op ← open_constn c (num_binders c),
prf' ← mk_mapp ``fin_to_pos_helper [some (type op.1), some (prf op.1)],
type' ← return (imp (app (const ``not []) (type op.1)) (const ``false [])),
return $ close_constn (mk 0 1 ff prf' type') op.2

private meta_definition focus' (c : cls) (i : nat) : tactic cls := do
@guard tactic _ (lit.is_pos (get_lit c i) = tt) _,
op ← open_constn c (num_lits c),
hyp_i ← option.to_monad (list.nth op.2 i),
prf' ← mk_mapp ``classical.by_contradiction [none, some (lambdas [hyp_i] (prf op.1))],
type' ← return (lit.formula (get_lit c i)),
return $ close_constn (mk 0 1 tt prf' type') (list.remove op.2 i)

meta_definition focus (c : cls) (i : nat) : tactic cls :=
if has_fin c = tt ∧ i+1 = num_lits c then
  return c
else if has_fin c = tt then
  do c' ← fin_to_pos c, focus' c' i
else
  focus' c i

end cls

meta_definition unify_lit (l1 l2 : cls.lit) : tactic unit :=
if cls.lit.is_pos l1 = cls.lit.is_pos l2 then
  unify (cls.lit.formula l1) (cls.lit.formula l2)
else
  fail "cannot unify literals"

-- FIXME: this is most definitely broken with meta-variables that were already in the goal
meta_definition sort_and_constify_metas : list expr → tactic (list expr)
| exprs_with_metas := do
inst_exprs ← @mapM tactic _ _ _ instantiate_mvars exprs_with_metas,
metas ← return $ inst_exprs >>= get_metas,
match list.filter (λm, has_meta_var (get_meta_type m) = ff) metas with
| [] :=
     if list.empty metas = tt then
       return []
     else do
       forM' metas (λm, do trace (expr.to_string m), t ← infer_type m, trace (expr.to_string t)),
       fail "could not sort metas"
| ((meta n t) :: _) := do
  t' ← infer_type (meta n t),
  uniq ← mk_fresh_name,
  c ← return (local_const uniq uniq binder_info.default t'),
  unify c (meta n t),
  rest ← sort_and_constify_metas metas,
  return (rest ++ [c])
| _ := failed
end
