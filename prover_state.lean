import clause lpo
open tactic monad

structure active_cls :=
(id : name)
(selected : list nat)
(c : cls)

private meta def active_cls_tactic_format (c : active_cls) : tactic format := do
c_fmt ← pp (active_cls.c c),
return $ c_fmt ++ to_fmt " (selected: " ++ to_fmt (active_cls.selected c) ++ to_fmt ")"

meta instance : has_to_tactic_format active_cls :=
⟨active_cls_tactic_format⟩

structure resolution_prover_state :=
(active : rb_map name active_cls)
(passive : rb_map name cls)
(newly_derived : list cls)
(prec : list expr)
(age : nat)

open resolution_prover_state

private meta def join_with_nl : list format → format :=
list.foldl (λx y, x ++ format.line ++ y) format.nil

private meta def resolution_prover_state_tactic_fmt (s : resolution_prover_state) : tactic format := do
active_fmts ← mapM pp (rb_map.values s↣active),
passive_fmts ← mapM pp (rb_map.values s↣passive),
new_fmts ← mapM pp s↣newly_derived,
prec_fmts ← mapM pp s↣prec,
return (join_with_nl
  ([to_fmt "active:"] ++ map (append (to_fmt "  ")) active_fmts ++
  [to_fmt "passive:"] ++ map (append (to_fmt "  ")) passive_fmts ++
  [to_fmt "new:"] ++ map (append (to_fmt "  ")) new_fmts ++
  [to_fmt "precedence order: " ++ to_fmt prec_fmts]))

meta instance : has_to_tactic_format resolution_prover_state :=
⟨resolution_prover_state_tactic_fmt⟩

meta def resolution_prover :=
stateT resolution_prover_state tactic

meta instance : monad resolution_prover := stateT.monad _ _

meta def resolution_prover_of_tactic {a} (tac : tactic a) : resolution_prover a :=
λs, do res ← tac, return (res, s)

meta def resolution_prover.fail {A B : Type} [has_to_format B] (msg : B) : resolution_prover A :=
resolution_prover_of_tactic (tactic.fail msg)

meta def resolution_prover.failed {A : Type} : resolution_prover A :=
resolution_prover.fail "failed"

meta def resolution_prover.orelse {A : Type} (p1 p2 : resolution_prover A) : resolution_prover A :=
take state, p1 state <|> p2 state

meta instance : alternative resolution_prover :=
alternative.mk (@monad.map _ _)
  (@applicative.pure _ (monad_is_applicative resolution_prover))
  (@applicative.seq _ (monad_is_applicative resolution_prover))
  @resolution_prover.failed
  @resolution_prover.orelse

meta def get_active : resolution_prover (rb_map name active_cls) :=
do state ← stateT.read, return state↣active

meta def add_active (a : active_cls) : resolution_prover unit :=
do state ← stateT.read,
stateT.write { state with active := state↣active↣insert a↣id a }

meta def get_passive : resolution_prover (rb_map name cls) :=
liftM passive stateT.read

private meta def add_passive (id : name) (c : cls) : resolution_prover unit :=
do state ← stateT.read, stateT.write { state with passive := rb_map.insert state↣passive id c }

private meta def get_new_cls_id : resolution_prover name := do
state ← stateT.read,
stateT.write { state with age := state↣age + 1 },
cls_prefix ← resolution_prover_of_tactic $ get_unused_name `cls none,
return $ mk_num_name cls_prefix state↣age

meta def register_as_passive (c : cls) : resolution_prover name := do
id ← get_new_cls_id,
resolution_prover_of_tactic (assertv id c↣type c↣prf),
prf' ← resolution_prover_of_tactic (get_local id),
resolution_prover_of_tactic $ infer_type prf', -- FIXME: otherwise ""
add_passive id { c with prf := prf' },
return id

meta def remove_passive (id : name) : resolution_prover unit :=
do state ← stateT.read, stateT.write { state with passive := state↣passive↣erase id }

meta def take_newly_derived : resolution_prover (list cls) := do
state ← stateT.read,
stateT.write { state with newly_derived := [] },
return state↣newly_derived

meta def remove_redundant (id : name) : resolution_prover unit := do
resolution_prover_of_tactic (get_local id >>= clear),
state ← stateT.read,
stateT.write { state with active := state↣active↣erase id }

meta def get_precedence : resolution_prover (list expr) :=
do state ← stateT.read, return state↣prec

meta def get_term_order : resolution_prover (expr → expr → bool) := do
state ← stateT.read,
return $ lpo (prec_gt_of_name_list (map name_of_funsym state↣prec))

private meta def set_precedence (new_prec : list expr) : resolution_prover unit :=
do state ← stateT.read, stateT.write { state with prec := new_prec }

meta def register_consts_in_precedence (consts : list expr) := do
p ← get_precedence,
p_set ← return (rb_map.set_of_list (map name_of_funsym p)),
new_syms ← return $ list.filter (λc, ¬p_set↣contains (name_of_funsym c)) consts,
set_precedence (new_syms ++ p)

meta def add_inferred (c : cls) : resolution_prover unit := do
c' ← resolution_prover_of_tactic c↣normalize,
register_consts_in_precedence (contained_funsyms c'↣type)↣values,
state ← stateT.read,
stateT.write { state with newly_derived := c' :: state↣newly_derived }

meta def inference :=
active_cls → resolution_prover unit

meta def seq_inferences : list inference → inference
| [] := λgiven, return ()
| (inf::infs) := λgiven, do
    inf given,
    now_active ← get_active,
    if rb_map.contains now_active given↣id then
      seq_inferences infs given
    else
      return ()

meta def redundancy_inference (is_redundant : active_cls → resolution_prover bool) : inference :=
λgiven, do
is_red ← is_redundant given,
if is_red then remove_redundant given↣id else return ()

meta def simp_inference (simpl : active_cls → resolution_prover (option cls)) : inference :=
λgiven, do maybe_simpld ← simpl given,
match maybe_simpld with
| some simpld := do add_inferred simpld, remove_redundant given↣id
| none := return ()
end

meta def selection_strategy := cls → resolution_prover (list nat)

meta def preprocessing_rule (f : list cls → resolution_prover (list cls)) : resolution_prover unit := do
state ← stateT.read,
newly_derived' ← f state↣newly_derived,
state' ← stateT.read,
stateT.write { state' with newly_derived := newly_derived' }

meta def clause_selection_strategy := ℕ → resolution_prover name

namespace resolution_prover_state

meta def empty : resolution_prover_state :=
{ active := rb_map.mk _ _, passive := rb_map.mk _ _,
  newly_derived := [], prec := [], age := 0 }

meta def initial (clauses : list cls) : tactic resolution_prover_state := do
after_setup ← forM' clauses add_inferred empty,
return after_setup.2

end resolution_prover_state
