import clause
open tactic monad

structure active_cls :=
(id : name)
(selected : list nat)
(c : cls)

private meta_definition active_cls_tactic_format (c : active_cls) : tactic format := do
c_fmt ← pp (active_cls.c c),
return $ c_fmt ++ to_fmt " (selected: " ++ to_fmt (active_cls.selected c) ++ to_fmt ")"

attribute [instance]
meta_definition active_cls_has_to_tactic_format : has_to_tactic_format active_cls :=
has_to_tactic_format.mk active_cls_tactic_format

structure resolution_prover_state :=
(active : rb_map name active_cls)
(passive : rb_map name cls)
(newly_derived : list cls)

open resolution_prover_state

private meta_definition join_with_nl : list format → format :=
list.foldl (λx y, x ++ format.line ++ y) format.nil

private meta_definition resolution_prover_state_tactic_fmt (s : resolution_prover_state) : tactic format := do
active_fmts ← @mapM tactic _ _ _ pp (rb_map.values (active s)),
passive_fmts ← @mapM tactic _ _ _ pp (rb_map.values (passive s)),
new_fmts ← @mapM tactic _ _ _ pp (newly_derived s),
return (join_with_nl
  ([to_fmt "active:"] ++ map (append (to_fmt "  ")) active_fmts ++
  [to_fmt "passive:"] ++ map (append (to_fmt "  ")) passive_fmts ++
  [to_fmt "new:"] ++ map (append (to_fmt "  ")) new_fmts) ++ format.line)

attribute [instance]
meta_definition resolution_prover_state_has_to_tactic_format : has_to_tactic_format resolution_prover_state :=
has_to_tactic_format.mk resolution_prover_state_tactic_fmt

meta_definition resolution_prover :=
stateT resolution_prover_state tactic

attribute [instance]
meta_definition resolution_prover_is_monad : monad resolution_prover :=
stateT_is_monad _ _

meta_definition resolution_prover_of_tactic {a} (tac : tactic a) : resolution_prover a :=
λs, do res ← tac, return (res, s)

meta_definition resolution_prover.fail {A B : Type} [has_to_format B] (msg : B) : resolution_prover A :=
resolution_prover_of_tactic (tactic.fail msg)

meta_definition resolution_prover.failed {A : Type} : resolution_prover A :=
resolution_prover.fail "failed"

meta_definition resolution_prover.orelse {A : Type} (p1 p2 : resolution_prover A) : resolution_prover A :=
take state, p1 state <|> p2 state

attribute [instance]
meta_definition resolution_prover_is_alternative : alternative resolution_prover :=
alternative.mk (@monad.map _ resolution_prover_is_monad)
  (@applicative.pure _ (monad_is_applicative resolution_prover))
  (@applicative.seq _ (monad_is_applicative resolution_prover))
  @resolution_prover.failed
  @resolution_prover.orelse

meta_definition get_active : resolution_prover (rb_map name active_cls) :=
do state ← stateT.read, return (active state)

meta_definition add_active (a : active_cls) : resolution_prover unit :=
@monad.bind resolution_prover _ _ _ stateT.read (λstate,
stateT.write (mk (rb_map.insert (active state) (active_cls.id a) a) (passive state) (newly_derived state)))

meta_definition get_passive : resolution_prover (rb_map name cls) :=
do state ← stateT.read, return (passive state)

private meta_definition add_passive (id : name) (c : cls) : resolution_prover unit :=
@monad.bind resolution_prover _ _ _ stateT.read (λstate,
stateT.write (mk (active state) (rb_map.insert (passive state) id c) (newly_derived state)))

meta_definition register_as_passive (c : cls) : resolution_prover name := do
id ← resolution_prover_of_tactic mk_fresh_name,
resolution_prover_of_tactic (assertv id (cls.type c) (cls.prf c)),
prf' ← resolution_prover_of_tactic (get_local id),
add_passive id (cls.mk (cls.num_quants c) (cls.num_lits c) prf' (cls.type c)),
return id

meta_definition remove_passive (id : name) : resolution_prover unit :=
@monad.bind resolution_prover _ _ _ stateT.read (λstate,
stateT.write (mk (active state) (rb_map.erase (passive state) id) (newly_derived state)))

meta_definition take_newly_derived : resolution_prover (list cls) :=
@monad.bind resolution_prover _ _ _ stateT.read (λstate,
@monad.bind resolution_prover _ _ _ (stateT.write (mk (active state) (passive state) []))
(λx, return (newly_derived state)))

example : resolution_prover (rb_map name active_cls) :=
@orelse resolution_prover _ _ get_active resolution_prover.failed

meta_definition remove_redundant (id : name) : resolution_prover unit := do
resolution_prover_of_tactic (get_local id >>= clear),
@monad.bind resolution_prover _ _ _ stateT.read (λstate,
stateT.write (mk (rb_map.erase (active state) id) (passive state) (newly_derived state)))

meta_definition add_inferred (c : cls) : resolution_prover unit := do
c' ← resolution_prover_of_tactic (cls.normalize c),
@monad.bind resolution_prover _ _ _ stateT.read (λstate,
stateT.write (mk (active state) (passive state) (c' :: newly_derived state)))

meta_definition inference :=
active_cls → resolution_prover unit

meta_definition list_contains {a} [decidable_eq a] (elem : a) (l : list a) : bool :=
match l with
| x::xs := if x = elem then tt else list_contains elem xs
| nil := ff
end

meta_definition seq_inferences : list inference → inference
| [] := λgiven, return ()
| (inf::infs) := λgiven, do
    inf given,
    now_active ← get_active,
    if rb_map.contains now_active (active_cls.id given) = tt then
      seq_inferences infs given
    else
      return ()

meta_definition redundancy_inference (is_redundant : active_cls → resolution_prover bool) : inference :=
λgiven, do
is_red ← is_redundant given,
if is_red = tt then remove_redundant (active_cls.id given) else return ()

meta_definition simp_inference (simpl : active_cls → resolution_prover (option cls)) : inference :=
λgiven, do maybe_simpld ← simpl given,
match maybe_simpld with
| some simpld := do add_inferred simpld, remove_redundant (active_cls.id given)
| none := return ()
end

meta_definition selection_strategy := cls → resolution_prover (list nat)

meta_definition dumb_selection : selection_strategy :=
λc, return $ match cls.lits_where c cls.lit.is_neg with
| [] := range (cls.num_lits c)
| neg_lit::_ := [neg_lit]
end

meta_definition preprocessing_rule (f : list cls → resolution_prover (list cls)) : resolution_prover unit := do
state ← stateT.read,
newly_derived' ← f (newly_derived state),
@monad.bind resolution_prover _ _ _ stateT.read (λstate',
stateT.write (mk (active state') (passive state') newly_derived'))

meta_definition clause_selection_strategy := resolution_prover name

meta_definition find_minimal_weight (passive : rb_map name cls) : name :=
match rb_map.fold passive none (λk c acc, match acc with
| none := some (k, expr_size (cls.type c))
| (some (n,s)) :=
    if expr_size (cls.type c) < s then
      some (k, expr_size (cls.type c))
    else
      acc
end) with
| none := name.anonymous
| some (n,_) := n
end

meta_definition weight_clause_selection : clause_selection_strategy :=
@monad.bind resolution_prover _ _ _ stateT.read (λstate,
return (find_minimal_weight (passive state)))
