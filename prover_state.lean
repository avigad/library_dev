import clause

structure active_cls :=
(id : name)
(selected : list nat)
(c : cls)

structure resolution_prover_state :=
(active : rb_map name active_cls)
(passive : rb_map name cls)

meta_definition resolution_prover :=
stateT resolution_prover_state tactic

attribute [instance]
meta_definition resolution_prover_is_monad : monad resolution_prover :=
stateT_is_monad _ _

meta_definition get_active : resolution_prover (rb_map name active_cls) :=
do state ← stateT.read, return (resolution_prover_state.active state)

meta_definition resolution_prover_of_tactic {a} (tac : tactic a) : resolution_prover a :=
λs, do res ← tac, return (res, s)

meta_definition inference :=
active_cls → resolution_prover (list cls × list name)

meta_definition list_contains {a} [decidable_eq a] (elem : a) (l : list a) : bool :=
match l with
| x::xs := if x = elem then tt else list_contains elem xs
| nil := ff
end

meta_definition seq_inferences (infs : list inference) : inference :=
λgiven, match infs with
| [] := return ([], [])
| inf::infs' := do
    (newly_derived, redundant) ← inf given,
    if list_contains (active_cls.id given) redundant = tt then
      return (newly_derived, redundant)
    else do
      (newly_derived', redundant') ← seq_inferences infs' given,
      return (newly_derived ++ newly_derived', redundant ++ redundant')
end

meta_definition redundancy_inference (is_redundant : active_cls → resolution_prover bool) : inference :=
λgiven, do
is_red ← is_redundant given,
return ([], if is_red = tt then [active_cls.id given] else [])

meta_definition simp_inference (simpl : active_cls → resolution_prover (option cls)) : inference :=
λgiven, do
maybe_simpld ← simpl given,
match maybe_simpld with
| some simpld := return ([simpld], [active_cls.id given])
| none := return ([], [])
end

meta_definition selection_strategy := cls → resolution_prover (list nat)

meta_definition dumb_selection : selection_strategy :=
λc, return $ match cls.lits_where c cls.lit.is_neg with
| [] := range (cls.num_lits c)
| neg_lit::_ := [neg_lit]
end

meta_definition preprocessing_rule := list cls → resolution_prover (list cls)
