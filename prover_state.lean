import clause

structure active_cls :=
(id : name)
(selected : list nat)
(c : cls)

structure resolution_prover_state :=
(active : rb_map name active_cls)
(passive : rb_map name cls)
(newly_derived : list cls)

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
do state ← stateT.read, return (resolution_prover_state.active state)

example : resolution_prover (rb_map name active_cls) :=
@orelse resolution_prover _ _ get_active resolution_prover.failed

meta_definition remove_redundant (n : name) : resolution_prover unit :=
@monad.bind resolution_prover _ _ _ stateT.read (λstate,
stateT.write (resolution_prover_state.mk (rb_map.erase (resolution_prover_state.active state) n)
  (resolution_prover_state.passive state) (resolution_prover_state.newly_derived state)))

meta_definition add_inferred (c : cls) : resolution_prover unit :=
@monad.bind resolution_prover _ _ _ stateT.read (λstate,
stateT.write (resolution_prover_state.mk (resolution_prover_state.active state)
  (resolution_prover_state.passive state) (c :: resolution_prover_state.newly_derived state)))

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
newly_derived' ← f (resolution_prover_state.newly_derived state),
@monad.bind resolution_prover _ _ _ stateT.read (λstate',
stateT.write (resolution_prover_state.mk (resolution_prover_state.active state')
  (resolution_prover_state.passive state') newly_derived'))
