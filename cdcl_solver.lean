import clause
open tactic expr monad

namespace cdcl

@[reducible] def prop_var := expr
@[reducible] def proof_term := expr
@[reducible] def proof_hyp := expr

inductive trail_elem
| dec : prop_var → bool → proof_hyp → trail_elem
| propg : prop_var → bool → proof_term → proof_hyp → trail_elem
| dbl_neg_propg : prop_var → bool → proof_term → proof_hyp → trail_elem

namespace trail_elem

def var : trail_elem → prop_var
| (dec v _ _) := v
| (propg v _ _ _) := v
| (dbl_neg_propg v _ _ _) := v

def phase : trail_elem → bool
| (dec _ ph _) := ph
| (propg _ ph _ _) := ph
| (dbl_neg_propg _ ph _ _) := ph

def hyp : trail_elem → proof_hyp
| (dec _ _ h) := h
| (propg _ _ _ h) := h
| (dbl_neg_propg _ _ _ h) := h

def is_decision : trail_elem → bool
| (dec _ _ _) := tt
| (propg _ _ _ _) := ff
| (dbl_neg_propg _ _ _ _) := ff

end trail_elem

structure var_state :=
(phase : bool)
(assigned : option proof_hyp)

structure learned_clause :=
(c : cls)
(actual_proof : proof_term)

inductive prop_lit
| neg : prop_var → prop_lit
| pos : prop_var → prop_lit

namespace prop_lit

meta instance : has_ordering prop_lit :=
⟨λl₁ l₂, match l₁, l₂ with
| pos _, neg _ := ordering.gt
| neg _, pos _ := ordering.lt
| pos v₁, pos v₂ := has_ordering.cmp v₁ v₂
| neg v₁, neg v₂ := has_ordering.cmp v₁ v₂
end⟩

meta def of_cls_lit : cls.lit → prop_lit
| (cls.lit.left v) := neg v
| (cls.lit.right v) := pos v
| (cls.lit.final v) := pos v

meta def of_var_and_phase (v : prop_var) : bool → prop_lit
| tt := pos v
| ff := neg v

end prop_lit

meta def watch_map := rb_map name (ℕ × ℕ × cls)

structure state :=
(trail : list trail_elem)
(vars : rb_map prop_var var_state)
(unassigned : rb_map prop_var prop_var)
(given : list cls)
(learned : list learned_clause)
(watches : rb_map prop_lit watch_map)
(conflict : option proof_term)
(unitp_queue : list prop_var)

namespace state

meta def initial : state := {
  trail := [],
  vars := rb_map.mk _ _,
  unassigned := rb_map.mk _ _,
  given := [],
  learned := [],
  watches := rb_map.mk _ _,
  conflict := none,
  unitp_queue := []
}

meta def watches_for (st : state) (pl : prop_lit) : watch_map :=
(st↣watches↣find pl)↣get_or_else (rb_map.mk _ _)

end state

meta def solver := stateT state tactic

meta instance : monad solver := stateT.monad _ _

meta def solver_of_tactic {A} (tac : tactic A) : solver A :=
take st, do res ← tac, return (res, st)

meta def mk_var_core (v : prop_var) (ph : bool) : solver unit := do
stateT.modify $ λst, match st↣vars↣find v with
| (some _) := st
| none := { st with
    vars := st↣vars↣insert v ⟨ph, none⟩,
    unassigned := st↣unassigned↣insert v v
  }
end

meta def mk_var (v : prop_var) : solver unit := mk_var_core v ff

meta def set_conflict (prf : proof_term) : solver unit :=
stateT.modify $ λst, { st with conflict := some prf }

meta def has_conflict : solver bool :=
do st ← stateT.read, return st↣conflict↣is_some

meta def push_trail (elem : trail_elem) : solver unit := do
st ← stateT.read,
match st↣vars↣find elem↣var with
| none := solver_of_tactic (fail $ "unknown variable: " ++ elem↣var↣to_string)
| some ⟨_, some _⟩ := solver_of_tactic (fail $ "adding already assigned variable to trail: " ++ elem↣var↣to_string)
| some ⟨_, none⟩ :=
  stateT.write { st with
    vars := st↣vars↣insert elem↣var ⟨elem↣phase, some elem↣hyp⟩,
    unassigned := st↣unassigned↣erase elem↣var,
    trail := elem :: st↣trail,
    unitp_queue := elem↣var :: st↣unitp_queue
  }
end

meta def pop_trail_core : solver (option trail_elem) := do
st ← stateT.read,
match st↣trail with
| elem :: rest := do
  stateT.write { st with trail := rest,
    vars := st↣vars↣insert elem↣var ⟨elem↣phase, none⟩,
    unassigned := st↣unassigned↣insert elem↣var elem↣var,
    unitp_queue := [] },
  return $ some elem
| [] := return none
end

meta def is_decision_level_zero : solver bool :=
do st ← stateT.read, return $ st↣trail↣for_all (λelem, ¬elem↣is_decision)

meta def revert_to_decision_level_zero : unit → solver unit | () := do
is_dl0 ← is_decision_level_zero,
if is_dl0 then return ()
else do pop_trail_core, revert_to_decision_level_zero ()

meta def formula_of_lit (v : prop_var) (ph : bool) :=
if ph then v else imp v false_

meta def lookup_var (v : prop_var) : solver (option var_state) :=
do st ← stateT.read, return $ st↣vars↣find v

meta def add_propagation (v : prop_var) (ph : bool) (just : proof_term) (just_is_dn : bool) : solver unit :=
do v_st ← lookup_var v, match v_st with
| none := solver_of_tactic (fail $ "propagating unknown variable: " ++ v↣to_string)
| some ⟨assg_ph, some prf⟩ :=
    if ph = assg_ph then
      return ()
    else if assg_ph ∧ ¬just_is_dn then
      set_conflict (app just prf)
    else
      set_conflict (app prf just)
| some ⟨_, none⟩ := do
    hyp_name ← solver_of_tactic mk_fresh_name,
    hyp ← return $ local_const hyp_name hyp_name binder_info.default (formula_of_lit v ph),
    if just_is_dn then do
      push_trail $ trail_elem.dbl_neg_propg v ph just hyp
    else do
      push_trail $ trail_elem.propg v ph just hyp
end

meta def add_decision (v : prop_var) (ph : bool) := do
hyp_name ← solver_of_tactic mk_fresh_name,
hyp ← return $ local_const hyp_name hyp_name binder_info.default (formula_of_lit v ph),
push_trail $ trail_elem.dec v ph hyp

meta def lookup_lit (l : cls.lit) : solver (option (bool × proof_hyp)) :=
do var_st_opt ← lookup_var l↣formula, match var_st_opt with
| none := return none
| some ⟨ph, none⟩ := return none
| some ⟨ph, some prf⟩ :=
  return $ some (if l↣is_neg then bnot ph else ph, prf)
end

meta def lit_is_false (l : cls.lit) : solver bool :=
do s ← lookup_lit l, return $ match s with
| some (ff, _) := tt
| _ := ff
end

meta def lit_is_not_false (l : cls.lit) : solver bool :=
do isf ← lit_is_false l, return $ bnot isf

meta def cls_is_false (c : cls) : solver bool :=
liftM list.band $ mapM lit_is_false c↣get_lits

private meta def unit_propg_cls' : cls → solver (option prop_var) | c :=
if c↣num_lits = 0 then return (some c↣prf)
else let hd := c↣get_lit 0 in
do lit_st ← lookup_lit hd, match lit_st with
| some (ff, isf_prf) :=
  if hd↣is_final then
    return (some $ app isf_prf c↣prf)
  else
    unit_propg_cls' (c↣inst isf_prf)
| _                  := return none
end

meta def unit_propg_cls : cls → solver unit | c :=
do has_confl ← has_conflict,
if has_confl then return () else
if c↣num_lits = 0 then do set_conflict c↣prf
else let hd := c↣get_lit 0 in
do lit_st ← lookup_lit hd, match lit_st with
| some (ff, isf_prf) :=
  if hd↣is_final then
    set_conflict (app isf_prf c↣prf)
  else
    unit_propg_cls (c↣inst isf_prf)
| some (tt, _) := return ()
| none :=
if c↣num_lits = 1 ∧ c↣has_fin then
  add_propagation c↣type tt c↣prf ff
else do fls_prf_opt ← unit_propg_cls' (c↣inst (expr.mk_var 0)),
match fls_prf_opt with
| some fls_prf := do
fls_prf' ← return $ lam `H binder_info.default c↣type↣binding_domain fls_prf,
if hd↣is_neg then
  add_propagation hd↣formula ff fls_prf' ff
else
  add_propagation hd↣formula tt fls_prf' tt
| none := return ()
end
end

private meta def modify_watches_for (pl : prop_lit) (f : watch_map → watch_map) : solver unit :=
stateT.modify $ λst, { st with
  watches := st↣watches↣insert pl (f $ st↣watches_for pl)
}

private meta def add_watch (n : name) (c : cls) (i j : ℕ) : solver unit :=
let l := c↣get_lit i, pl := prop_lit.of_cls_lit l in
modify_watches_for pl $ λw, w↣insert n (i,j,c)

private meta def remove_watch (n : name) (c : cls) (i : ℕ) : solver unit :=
let l := c↣get_lit i, pl := prop_lit.of_cls_lit l in
modify_watches_for pl $ λw, w↣erase n

private meta def set_watches (n : name) (c : cls) : solver unit :=
if c↣num_lits = 0 then
  set_conflict c↣prf
else if c↣num_lits = 1 then
  unit_propg_cls c
else do
  not_false_lits ← filterM (λi, lit_is_not_false (c↣get_lit i)) (list.range c↣num_lits),
  match not_false_lits with
  | [] := do
      add_watch n c 0 1,
      add_watch n c 1 0,
      unit_propg_cls c
  | [i] :=
      let j := if i = 0 then 1 else 0 in do
      add_watch n c i j,
      add_watch n c j i,
      unit_propg_cls c
  | (i::j::_) := do
      add_watch n c i j,
      add_watch n c j i
  end

meta def update_watches (n : name) (c : cls) (i₁ i₂ : ℕ) : solver unit := do
remove_watch n c i₁,
remove_watch n c i₂,
set_watches n c

meta def mk_clause (c : cls) : solver unit := do
forM c↣get_lits (λl, mk_var l↣formula),
revert_to_decision_level_zero (),
stateT.modify $ λst, { st with given := c :: st↣given },
c_name ← solver_of_tactic mk_fresh_name,
set_watches c_name c

meta def unit_propg_var (v : prop_var) : solver unit :=
do st ← stateT.read, if st↣conflict↣is_some then return () else
match st↣vars↣find v with
| some ⟨ph, none⟩ := solver_of_tactic $ fail ("propagating unassigned variable: " ++ v↣to_string)
| none := solver_of_tactic $ fail ("unknown variable: " ++ v↣to_string)
| some ⟨ph, some _⟩ :=
  let watches := st↣watches_for $ prop_lit.of_var_and_phase v (bnot ph) in
  forM' watches↣to_list $ λw, update_watches w↣1 w↣2↣2↣2 w↣2↣1 w↣2↣2↣1
end

meta def analyze_conflict' : proof_term → list trail_elem → cls
| prf (trail_elem.dec v ph hyp :: es) :=
  let abs_prf := abstract_local prf hyp↣local_uniq_name in
  if has_var abs_prf then
    cls.close_const (analyze_conflict' prf es) hyp
  else
    analyze_conflict' prf es
| prf (trail_elem.propg v ph l_prf hyp :: es) :=
  let abs_prf := abstract_local prf hyp↣local_uniq_name in
  if has_var abs_prf then
    analyze_conflict' (elet hyp↣local_pp_name (formula_of_lit v ph) l_prf abs_prf) es
  else
    analyze_conflict' prf es
| prf (trail_elem.dbl_neg_propg v ph l_prf hyp :: es) :=
  let abs_prf := abstract_local prf hyp↣local_uniq_name in
  if has_var abs_prf then
    analyze_conflict' (app l_prf (lambdas [hyp] prf)) es
  else
    analyze_conflict' prf es
| prf [] := ⟨0, 0, ff, prf, const ``false []⟩

meta def analyze_conflict (prf : proof_term) : solver cls :=
do st ← stateT.read, return $ analyze_conflict' prf st↣trail

meta def add_learned (c : cls) : solver unit := do
prf_abbrev_name ← solver_of_tactic mk_fresh_name,
c' ← return { c with prf := local_const prf_abbrev_name prf_abbrev_name binder_info.default c↣type },
stateT.modify $ λst, { st with learned := ⟨c', c↣prf⟩ :: st↣learned },
c_name ← solver_of_tactic mk_fresh_name,
set_watches c_name c'

meta def backtrack_with : cls → solver unit | conflict_clause := do
isf ← cls_is_false conflict_clause,
if ¬isf then
  stateT.modify (λst, { st with conflict := none })
else do
  removed_elem ← pop_trail_core,
  if removed_elem↣is_some then
    backtrack_with conflict_clause
  else
    return ()

meta def replace_learned_clauses' : proof_term → list learned_clause → proof_term
| prf [] := prf
| prf (⟨c, actual_proof⟩ :: lcs) :=
  let abs_prf := abstract_local prf c↣prf↣local_uniq_name in
  if has_var abs_prf then
    replace_learned_clauses' (elet c↣prf↣local_pp_name c↣type actual_proof abs_prf) lcs
  else
    replace_learned_clauses' prf lcs

meta def replace_learned_clauses (prf : proof_term) : solver proof_term :=
do st ← stateT.read, return $ replace_learned_clauses' prf st↣learned

inductive result
| unsat : proof_term → result
| sat : rb_map prop_var bool → result

variable theory_solver : solver (option proof_term)

meta def unit_propg : unit → solver unit | () := do
st ← stateT.read,
if st↣conflict↣is_some then return () else
match st↣unitp_queue with
| [] := return ()
| (v::vs) := do
  stateT.write { st with unitp_queue := vs },
  unit_propg_var v,
  unit_propg ()
end

private meta def run' : unit → solver result | () := do
unit_propg (),
st ← stateT.read,
match st↣conflict with
| some conflict := do
  conflict_clause ← analyze_conflict conflict,
  if conflict_clause↣num_lits = 0 then do
    prf ← replace_learned_clauses conflict_clause↣prf,
    return (result.unsat prf)
  else do
    backtrack_with conflict_clause,
    add_learned conflict_clause,
    run' ()
| none :=
  match st↣unassigned↣min with
  | none := do
    theory_conflict ← theory_solver,
    match theory_conflict with
    | some conflict := do set_conflict conflict, run' ()
    | none := return $ result.sat (st↣vars↣for (λvar_st, var_st↣phase))
    end
  | some unassigned :=
    match st↣vars↣find unassigned with
    | some ⟨ph, none⟩ := do add_decision unassigned ph, run' ()
    | _ := solver_of_tactic (fail "unassigned variable is assigned")
    end
  end
end

meta def run : solver result := run' theory_solver ()

meta def solve (given : list cls) : tactic result := do
res ← (do forM given mk_clause, run theory_solver) state.initial,
return res↣1

end cdcl
