import clause clausifier
open tactic expr monad

namespace dpll

inductive result
| sat : rb_map expr bool → result
| unsat : expr → result

structure state :=
(assg : rb_map expr (bool × expr))
(unassg : rb_map expr unit)
(clauses : list cls)

meta_definition state.initial (clauses : list cls) : state :=
{ assg := rb_map.mk _ _,
  unassg := rb_map.set_of_list (do c ← clauses, l ← cls.get_lits c, [cls.lit.formula l]),
  clauses := clauses }

inductive res A : Type
| running : state → A → res
| conflict : expr → res

namespace res
def map {A B : Type} (f : A → B) : res A → res B
| (running s a) := running s (f a)
| (conflict .A res) := conflict B res
end res

meta_definition st A := state → tactic (res A)

attribute [instance]
meta_definition st_is_monad : monad st :=
{ map := λ{A B} f g s, do { a ← g s, return (res.map f a) },
  ret := λ{A} x s, return (res.running s x),
  bind := λ{A B} g f s, do { ra ← g s,
       match ra with
       | res.running s' a := f a s'
       | res.conflict .A res := return $ res.conflict B res
       end } }

meta_definition st_of_tactic {A} (tac : tactic A) : st A :=
take s, liftM (res.running s) tac

meta_definition get_state : st state :=
take s, return (res.running s s)

meta_definition get_clauses : st (list cls) :=
do s ← get_state, return s↣clauses

meta_definition conflict {A} (prf : expr) : st A :=
take s, return (res.conflict _ prf)

meta_definition assign (v : expr) (phase : bool) (prf : expr) : st unit :=
take s, return $ res.running { s with
     unassg := rb_map.erase s↣unassg v,
     assg := rb_map.insert s↣assg v (phase, prf) } ()

meta_definition set_clauses (clauses : list cls) : st unit :=
take s, return $ res.running { s with clauses := clauses } ()

meta_definition get_lit_state (l : cls.lit) : st (option (bool × expr)) :=
do s ← get_state, return $
match rb_map.find s↣assg (cls.lit.formula l) with
| some (phase, expr) := some (decidable.to_bool (cls.lit.is_pos l = phase), expr)
| none := none
end

meta_definition is_lit_true (l : cls.lit) : st bool :=
do s ← get_lit_state l, return $
match s with
| some (val, _) := val
| none := ff
end

meta_definition is_cls_true (c : cls) : st bool :=
liftM list.bor $ mapM is_lit_true (cls.get_lits c)

private meta_definition unit_propg1' : cls → st (option expr) | c :=
if c↣num_lits = 0 then return (some c↣prf)
else let hd := cls.get_lit c 0 in
do isf ← get_lit_state hd, match isf with
| some (ff, isf_prf) := unit_propg1' (cls.inst c isf_prf)
| _                  := return none
end

meta_definition unit_propg1 : cls → st (option expr) | c :=
if c↣num_lits = 0 then conflict c↣prf
else let hd := cls.get_lit c 0 in
do isf ← get_lit_state hd, match isf with
| some (ff, isf_prf) := unit_propg1 (cls.inst c isf_prf)
| some (tt, _) := return none
| none := do fls_prf_opt ← unit_propg1' (cls.inst c (mk_var 0)),
match fls_prf_opt with
| some fls_prf := do
  fls_prf' ← return $ lam `H binder_info.default (binding_domain c↣type) fls_prf,
  prf ← return (if cls.lit.is_pos hd then
      app_of_list (const ``classical.by_contradiction []) [cls.lit.formula hd, fls_prf']
    else fls_prf'),
  assign (cls.lit.formula hd) (cls.lit.is_pos hd) prf,
  return (some $ cls.lit.formula hd)
| none := return none
end
end

meta_definition unit_propg : unit → st unit | () := do
propagated ← get_clauses >>= mapM unit_propg1,
if list.bor (list.map option.is_some propagated) then
  unit_propg ()
else
  return ()

meta_definition remove_satisfied : st unit := do
get_clauses >>= filterM (λc, liftM bool.bnot (is_cls_true c)) >>= set_clauses

meta_definition pick_unassg : st (option expr) :=
do s ← get_state, return $
match rb_map.keys s↣unassg with
| (v::_) := some v
| [] := none
end

meta_definition catch_conflict {A} (g : st A) : st (sum expr A) :=
take s, do r ← g s, match r with
| (res.conflict .A prf) := return (res.running s (sum.inl prf))
| (res.running s a) := return (res.running s (sum.inr a))
end

private meta_definition find_model' : unit → st (rb_map expr bool) | () := do
unit_propg (),
remove_satisfied,
v_opt ← pick_unassg,
match v_opt with
| none := do s ← get_state, return (rb_map.map (λv : bool × expr, v↣1) s↣assg)
| some v := do
  hv_n ← st_of_tactic mk_fresh_name,
  hv_e ← return $ local_const hv_n hv_n binder_info.default v,
  -- first try v_e ↦ tt
  tt_case ← catch_conflict (do assign v tt hv_e, find_model' ()),
  match tt_case with
  | sum.inr model := return model
  | sum.inl tt_prf :=
    if ¬has_var (abstract_local tt_prf hv_n) then
      conflict tt_prf
    else do
      hnv_n ← st_of_tactic mk_fresh_name,
      hnv_e ← return $ local_const hv_n hv_n binder_info.default (enot v),
      ff_case ← catch_conflict (do assign v ff hnv_e, find_model' ()),
      match ff_case with
      | sum.inr model := return model
      | sum.inl ff_prf := do
        conflict $ app_of_list (const ``classical.by_cases [])
                               [v, const ``false [], lambdas [hv_e] tt_prf, lambdas [hnv_e] ff_prf]
      end
  end
end

meta_definition solve (clauses : list cls) : tactic result := do
res ← find_model' () (state.initial clauses),
match res with
| (res.conflict .(rb_map expr bool) prf) := return (result.unsat prf)
| (res.running _ interp) := return (result.sat interp)
end

end dpll

meta_definition dpll : tactic unit := do
intros,
target_name ← get_unused_name `target none, tgt ← target,
mk_mapp ``classical.by_contradiction [some tgt] >>= apply, intro target_name,
hyps ← local_context,
gen_clauses ← mapM cls.of_proof hyps,
clauses ← clausify gen_clauses,
no_fin_clauses ← collect_successes $ map cls.fin_to_pos clauses,
res ← dpll.solve no_fin_clauses,
match res with
| (dpll.result.unsat prf) := exact prf
| (dpll.result.sat interp) :=
  let interp' := map (λe : expr × bool, if e↣2 = tt then e↣1 else enot e↣1) (rb_map.to_list interp) in
  do pp_interp ← pp interp',
     fail (to_fmt "satisfying assignment: " ++ pp_interp)
end

-- FIXME: using example here hid some type-checking errors???
namespace dpll
lemma example0 {a} : a → ¬a → false := by dpll
lemma example1 {a} : a ∨ ¬a := by dpll
lemma example2 {a b : Prop} : a → (a → b) → b := by dpll
lemma example3 {a b c : Prop} : (a → b) → (¬a → b) → (b → c) → b ∧ c := by dpll
end dpll
