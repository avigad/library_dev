import clause clausifier
open tactic expr monad

namespace cdcl

@[reducible] def prop_var := expr
@[reducible] def proof_term := expr
@[reducible] def proof_hyp := expr

inductive trail_elem
| dec : prop_var → bool → proof_hyp → trail_elem
| propg : prop_var → bool → proof_term → proof_hyp → trail_elem

namespace trail_elem

def var : trail_elem → prop_var
| (dec v _ _) := v
| (propg v _ _ _) := v

def phase : trail_elem → bool
| (dec _ ph _) := ph
| (propg _ ph _ _) := ph

def hyp : trail_elem → proof_hyp
| (dec _ _ h) := h
| (propg _ _ _ h) := h

def is_decision : trail_elem → bool
| (dec _ _ _) := tt
| (propg _ _ _ _) := ff

end trail_elem

structure var_state :=
(phase : bool)
(assigned : option proof_hyp)

structure learned_clause :=
(c : cls)
(actual_proof : proof_term)

structure state :=
(trail : list trail_elem)
(vars : rb_map prop_var var_state)
(unassigned : rb_map prop_var prop_var)
(given : list cls)
(learned : list learned_clause)
(conflict : option proof_term)
(unitp_queue : list prop_var)

meta def state.initial : state := {
  trail := [],
  vars := rb_map.mk _ _,
  unassigned := rb_map.mk _ _,
  given := [],
  learned := [],
  conflict := none,
  unitp_queue := []
}

meta def solver := stateT state tactic

meta instance : monad solver := stateT.monad _ _

meta def solver_of_tactic {A} (tac : tactic A) : solver A :=
take st, do res ← tac, return (res, st)

meta def mk_var_core (v : prop_var) (ph : bool) : solver unit := do
st ← stateT.read, match st↣vars↣find v with
| (some _) := return ()
| none := stateT.write { st with
    vars := st↣vars↣insert v ⟨ph, none⟩,
    unassigned := st↣unassigned↣insert v v
  }
end

meta def mk_var (v : prop_var) : solver unit := mk_var_core v ff

meta def set_conflict (prf : proof_term) : solver unit :=
do st ← stateT.read, stateT.write { st with conflict := some prf }

meta def has_conflict : solver bool :=
do st ← stateT.read, return st↣conflict↣is_some

meta def push_trail (elem : trail_elem) : solver unit := do
st ← stateT.read,
match st↣vars↣find elem↣var with
| none := solver_of_tactic (fail $ "unknown variable: " ++ elem↣var↣to_string)
| some ⟨_, some _⟩ := solver_of_tactic (fail $ "already assigned: " ++ elem↣var↣to_string)
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
    unassigned := st↣unassigned↣insert elem↣var elem↣var },
  return $ some elem
| [] := return none
end

meta def is_decision_level_zero : solver bool :=
do st ← stateT.read, return (list.band $ st↣trail↣for (λelem, bool.bnot elem↣is_decision))

meta def revert_to_decision_level_zero : unit → solver unit | () := do
is_dl0 ← is_decision_level_zero,
if is_dl0 then return ()
else do pop_trail_core, revert_to_decision_level_zero ()

meta def mk_clause (c : cls) : solver unit := do
c' ← solver_of_tactic c↣fin_to_pos,
forM c'↣get_lits (λl, mk_var l↣formula),
revert_to_decision_level_zero (),
st ← stateT.read, stateT.write { st with
  given := c' :: st↣given,
  unitp_queue := c'↣get_lits↣for (λl, l↣formula) ++ st↣unitp_queue
}

meta def formula_of_lit (v : prop_var) (ph : bool) :=
if ph then v else enot v

meta def add_propagation (v : prop_var) (ph : bool) (just : proof_term) := do
hyp_name ← solver_of_tactic mk_fresh_name,
hyp ← return $ local_const hyp_name hyp_name binder_info.default (formula_of_lit v ph),
push_trail $ trail_elem.propg v ph just hyp

meta def add_decision (v : prop_var) (ph : bool) := do
hyp_name ← solver_of_tactic mk_fresh_name,
hyp ← return $ local_const hyp_name hyp_name binder_info.default (formula_of_lit v ph),
push_trail $ trail_elem.dec v ph hyp

meta def lookup_var (v : prop_var) : solver (option var_state) :=
do st ← stateT.read, return $ st↣vars↣find v

meta def lookup_lit (l : cls.lit) : solver (option (bool × proof_hyp)) :=
do var_st_opt ← lookup_var l↣formula, match var_st_opt with
| none := return none
| some ⟨ph, none⟩ := return none
| some ⟨ph, some prf⟩ :=
  return $ some (if l↣is_neg then bool.bnot ph else ph, prf)
end

meta def lit_is_false (l : cls.lit) : solver bool :=
do s ← lookup_lit l, return $ match s with
| some (ff, _) := tt
| _ := ff
end

meta def cls_is_false (c : cls) : solver bool :=
liftM list.band $ mapM lit_is_false c↣get_lits

private meta def unit_propg1' : cls → solver (option prop_var) | c :=
if c↣num_lits = 0 then return (some c↣prf)
else let hd := c↣get_lit 0 in
do lit_st ← lookup_lit hd, match lit_st with
| some (ff, isf_prf) := unit_propg1' (c↣inst isf_prf)
| _                  := return none
end

meta def unit_propg1 : cls → solver unit | c :=
do has_confl ← has_conflict,
if has_confl then return () else
if c↣num_lits = 0 then do set_conflict c↣prf
else let hd := c↣get_lit 0 in
do lit_st ← lookup_lit hd, match lit_st with
| some (ff, isf_prf) := unit_propg1 (c↣inst isf_prf)
| some (tt, _) := return ()
| none :=
do fls_prf_opt ← unit_propg1' (c↣inst (expr.mk_var 0)),
match fls_prf_opt with
| some fls_prf := do
  fls_prf' ← return $ lam `H binder_info.default c↣type↣binding_domain fls_prf,
  prf ← return (if hd↣is_pos then
    app_of_list (const ``classical.by_contradiction []) [hd↣formula, fls_prf']
    else fls_prf'),
  add_propagation hd↣formula hd↣is_pos prf
| none := return ()
end
end

meta def unit_propg : unit → solver unit | () :=
do st ← stateT.read,
if st↣conflict↣is_some ∨ st↣unitp_queue↣empty then return () else do
stateT.write { st with unitp_queue := [] },
forM st↣given unit_propg1,
forM st↣learned (λlc, unit_propg1 lc↣c),
unit_propg ()

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
| prf [] := ⟨0, 0, ff, prf, const ``false []⟩

meta def analyze_conflict (prf : proof_term) : solver cls :=
do st ← stateT.read, return $ analyze_conflict' prf st↣trail

meta def add_learned (c : cls) : solver unit := do
prf_abbrev_name ← solver_of_tactic mk_fresh_name,
c' ← return { c with prf := local_const prf_abbrev_name prf_abbrev_name binder_info.default c↣type },
st ← stateT.read, stateT.write { st with
  learned := ⟨c', c↣prf⟩ :: st↣learned,
  unitp_queue := c'↣get_lits↣for (λl, l↣formula) ++ st↣unitp_queue
}

meta def backtrack_with : cls → solver unit | conflict_clause := do
isf ← cls_is_false conflict_clause,
if ¬isf then do
  st ← stateT.read,
  stateT.write { st with conflict := none }
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

private meta def theory_solver_of_tactic (th_solver : tactic unit) : cdcl.solver (option cdcl.proof_term) :=
do s ← stateT.read, cdcl.solver_of_tactic $ do
hyps ← return $ s↣trail↣for (λe, e↣hyp),
subgoal ← mk_meta_var (const ``false []),
goals ← get_goals,
set_goals [subgoal],
hvs ← forM hyps (λhyp, assertv hyp↣local_pp_name hyp↣local_type hyp),
solved ← (do th_solver, now, return tt) <|> return ff,
set_goals goals,
if solved then do
  prf ← instantiate_mvars subgoal,
  prf' ← whnf prf, -- gets rid of the unnecessary asserts
  return $ some prf'
else
  return none

meta def cdcl_t (th_solver : tactic unit) : tactic unit := do
intros,
target_name ← get_unused_name `target none, tgt ← target,
mk_mapp ``classical.by_contradiction [some tgt] >>= apply, intro target_name,
hyps ← local_context,
gen_clauses ← mapM cls.of_proof hyps,
clauses ← clausify gen_clauses,
no_fin_clauses ← collect_successes $ map cls.fin_to_pos clauses,
res ← cdcl.solve (theory_solver_of_tactic th_solver) no_fin_clauses,
match res with
| (cdcl.result.unsat prf) := exact prf
| (cdcl.result.sat interp) :=
  let interp' := do e ← interp↣to_list, [if e↣2 = tt then e↣1 else enot e↣1] in
  do pp_interp ← pp interp',
     fail (to_fmt "satisfying assignment: " ++ pp_interp)
end

meta def cdcl : tactic unit := cdcl_t skip

-- FIXME: using example here hides "contains local constants" errors
private lemma example1 {a} : a → ¬a → false := by cdcl
private lemma example2 {a} : a ∨ ¬a := by cdcl
private lemma example3 {a b : Prop} : a → (a → b) → b := by cdcl
private lemma example4 {a b c : Prop} : (a → b) → (¬a → b) → (b → c) → b ∧ c := by cdcl

private meta def lit_unification : tactic unit :=
do ls ← local_context, first $ do l ← ls, [do apply l, assumption]
private lemma example5 {p : ℕ → Prop} : p 2 ∨ p 4 → (p (2*2) → p (2+0)) → p (1+1) :=
by cdcl_t lit_unification
