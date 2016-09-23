import clause lpo
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
⟨active_cls_tactic_format⟩

structure resolution_prover_state :=
(active : rb_map name active_cls)
(passive : rb_map name cls)
(newly_derived : list cls)
(prec : list expr)
(age : nat)

open resolution_prover_state

private meta_definition join_with_nl : list format → format :=
list.foldl (λx y, x ++ format.line ++ y) format.nil

private meta_definition resolution_prover_state_tactic_fmt (s : resolution_prover_state) : tactic format := do
active_fmts ← mapM pp (rb_map.values s↣active),
passive_fmts ← mapM pp (rb_map.values s↣passive),
new_fmts ← mapM pp s↣newly_derived,
prec_fmts ← mapM pp s↣prec,
return (join_with_nl
  ([to_fmt "active:"] ++ map (append (to_fmt "  ")) active_fmts ++
  [to_fmt "passive:"] ++ map (append (to_fmt "  ")) passive_fmts ++
  [to_fmt "new:"] ++ map (append (to_fmt "  ")) new_fmts ++
  [to_fmt "precedence order: " ++ to_fmt prec_fmts]))

attribute [instance]
meta_definition resolution_prover_state_has_to_tactic_format : has_to_tactic_format resolution_prover_state :=
⟨resolution_prover_state_tactic_fmt⟩

meta_definition resolution_prover :=
stateT resolution_prover_state tactic

attribute [instance]
meta_definition resolution_prover_is_monad : monad resolution_prover :=
⟨@stateT_fmap _ _ _, @stateT_return _ _ _, @stateT_bind _ _ _⟩

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
do state ← stateT.read,
stateT.write { state with active := rb_map.insert state↣active a↣id a }

meta_definition get_passive : resolution_prover (rb_map name cls) :=
liftM passive stateT.read

private meta_definition add_passive (id : name) (c : cls) : resolution_prover unit :=
do state ← stateT.read, stateT.write { state with passive := rb_map.insert state↣passive id c }

private meta_definition get_new_cls_id : resolution_prover name := do
state ← stateT.read,
stateT.write { state with age := state↣age + 1 },
cls_prefix ← resolution_prover_of_tactic $ get_unused_name `cls none,
return $ mk_num_name cls_prefix state↣age

meta_definition register_as_passive (c : cls) : resolution_prover name := do
id ← get_new_cls_id,
resolution_prover_of_tactic (assertv id c↣type c↣prf),
prf' ← resolution_prover_of_tactic (get_local id),
resolution_prover_of_tactic $ infer_type prf', -- FIXME: otherwise ""
add_passive id { c with prf := prf' },
return id

meta_definition remove_passive (id : name) : resolution_prover unit :=
do state ← stateT.read, stateT.write { state with passive := rb_map.erase state↣passive id }

meta_definition take_newly_derived : resolution_prover (list cls) := do
state ← stateT.read,
stateT.write { state with newly_derived := [] },
return state↣newly_derived

meta_definition remove_redundant (id : name) : resolution_prover unit := do
resolution_prover_of_tactic (get_local id >>= clear),
state ← stateT.read,
stateT.write { state with active := rb_map.erase state↣active id }

meta_definition get_precedence : resolution_prover (list expr) :=
do state ← stateT.read, return state↣prec

meta_definition get_term_order : resolution_prover (expr → expr → bool) := do
state ← stateT.read,
return $ lpo (prec_gt_of_name_list (map name_of_funsym state↣prec))

private meta_definition set_precedence (new_prec : list expr) : resolution_prover unit :=
do state ← stateT.read, stateT.write { state with prec := new_prec }

meta_definition register_consts_in_precedence (consts : list expr) := do
p ← get_precedence,
p_set ← return (rb_map.set_of_list (map name_of_funsym p)),
new_syms ← return $ list.filter (λc, ¬rb_map.contains p_set (name_of_funsym c)) consts,
set_precedence (new_syms ++ p)

meta_definition add_inferred (c : cls) : resolution_prover unit := do
c' ← resolution_prover_of_tactic (cls.normalize c),
register_consts_in_precedence (rb_map.values (contained_funsyms c'↣type)),
state ← stateT.read,
stateT.write { state with newly_derived := c' :: state↣newly_derived }

meta_definition inference :=
active_cls → resolution_prover unit

meta_definition seq_inferences : list inference → inference
| [] := λgiven, return ()
| (inf::infs) := λgiven, do
    inf given,
    now_active ← get_active,
    if rb_map.contains now_active given↣id then
      seq_inferences infs given
    else
      return ()

meta_definition redundancy_inference (is_redundant : active_cls → resolution_prover bool) : inference :=
λgiven, do
is_red ← is_redundant given,
if is_red then remove_redundant given↣id else return ()

meta_definition simp_inference (simpl : active_cls → resolution_prover (option cls)) : inference :=
λgiven, do maybe_simpld ← simpl given,
match maybe_simpld with
| some simpld := do add_inferred simpld, remove_redundant given↣id
| none := return ()
end

meta_definition selection_strategy := cls → resolution_prover (list nat)

meta_definition dumb_selection : selection_strategy :=
λc, return $ match cls.lits_where c cls.lit.is_neg with
| [] := list.range c↣num_lits
| neg_lit::_ := [neg_lit]
end

meta_definition selection21 : selection_strategy := take c, do
gt ← get_term_order,
maximal_lits ← return $ list.filter_maximal (λi j,
  gt (cls.lit.formula $ cls.get_lit c i) (cls.lit.formula $ cls.get_lit c j)) (list.range (cls.num_lits c)),
if list.length maximal_lits = 1 then return maximal_lits else do
neg_lits ← return $ list.filter (λi, cls.lit.is_neg (cls.get_lit c i)) (list.range (cls.num_lits c)),
maximal_neg_lits ← return $ list.filter_maximal (λi j,
  gt (cls.lit.formula $ cls.get_lit c i) (cls.lit.formula $ cls.get_lit c j)) neg_lits,
if ¬list.empty maximal_neg_lits then
  return (list.taken 1 maximal_neg_lits)
else
  return maximal_lits
meta_definition selection22 : selection_strategy := take c, do
gt ← get_term_order,
maximal_lits ← return $ list.filter_maximal (λi j,
  gt (cls.lit.formula $ cls.get_lit c i) (cls.lit.formula $ cls.get_lit c j)) (list.range (cls.num_lits c)),
maximal_lits_neg ← return $ list.filter (λi, cls.lit.is_neg (cls.get_lit c i)) maximal_lits,
if ¬list.empty maximal_lits_neg then
  return (list.taken 1 maximal_lits_neg)
else
  return maximal_lits

meta_definition preprocessing_rule (f : list cls → resolution_prover (list cls)) : resolution_prover unit := do
state ← stateT.read,
newly_derived' ← f state↣newly_derived,
state' ← stateT.read,
stateT.write { state' with newly_derived := newly_derived' }

meta_definition clause_selection_strategy := ℕ → resolution_prover name

meta_definition clause_weight (c : cls) : nat :=
40 * cls.num_lits c + expr_size (cls.type c)

meta_definition find_minimal_by (passive : rb_map name cls) (f : name → cls → ℕ) : name :=
match @rb_map.fold _ _ (option (name × ℕ)) passive none (λk c acc, match acc with
| none := some (k, f k c)
| (some (n,s)) :=
if f k c < s then
some (k, f k c)
else
acc
end) with
| none := name.anonymous
| some (n,_) := n
end

meta_definition age_of_clause_id : name → ℕ
| (name.mk_numeral i _) := unsigned.to_nat i
| _ := 0

meta_definition find_minimal_weight (passive : rb_map name cls) : name :=
find_minimal_by passive (λn c, 100 * clause_weight c + age_of_clause_id n)

meta_definition find_minimal_age (passive : rb_map name cls) : name :=
find_minimal_by passive (λn c, age_of_clause_id n)

meta_definition weight_clause_selection : clause_selection_strategy :=
take iter, do state ← stateT.read, return $ find_minimal_weight (passive state)

meta_definition oldest_clause_selection : clause_selection_strategy :=
take iter, do state ← stateT.read, return $ find_minimal_age state↣passive

meta_definition age_weight_clause_selection (thr mod : ℕ) : clause_selection_strategy :=
take iter, if iter % mod < thr then
              weight_clause_selection iter
           else
              oldest_clause_selection iter

namespace resolution_prover_state

meta_definition empty : resolution_prover_state :=
{ active := rb_map.mk _ _, passive := rb_map.mk _ _,
  newly_derived := [], prec := [], age := 0 }

meta_definition initial (clauses : list cls) : tactic resolution_prover_state := do
after_setup ← forM' clauses add_inferred empty,
return after_setup.2

end resolution_prover_state
