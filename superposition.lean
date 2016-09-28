import clause prover_state utils
open tactic monad expr

meta def get_rwr_positions : expr → list (list ℕ)
| (app a b) := [[]] ++
  do arg ← list.zip_with_index (get_app_args (app a b)),
     pos ← get_rwr_positions arg↣1,
     [arg↣2 :: pos]
| (mvar _ _) := []
| e := [[]]

meta def get_position : expr → list ℕ → expr
| (app a b) (p::ps) :=
match list.nth (get_app_args (app a b)) p with
| some arg := get_position arg ps
| none := (app a b)
end
| e _ := e

meta def replace_position (v : expr) : expr → list ℕ → expr
| (app a b) (p::ps) :=
let args := get_app_args (app a b) in
match list.nth args p with
| some arg := app_of_list (get_app_fn a) (list.update (replace_position arg ps) p args)
| none := app a b
end
| e [] := v
| e _ := e

variable gt : expr → expr → bool
variables (c1 c2 : clause)
variables (ac1 ac2 : active_cls)
variables (i1 i2 : nat)
variable pos : list ℕ
variable ltr : bool
variable congr_ax : name

lemma sup_f_ltr {A} {a1 a2} (f : A → Prop) (H : a1 = a2) : f a1 → f a2 := take Hfa1, H ▸ Hfa1
lemma sup_f_rtl {A} {a1 a2} (f : A → Prop) (H : a2 = a1) : f a1 → f a2 := sup_f_ltr f H↣symm

meta def is_eq_dir (e : expr) (ltr : bool) : option (expr × expr) :=
match is_eq e with
| some (lhs, rhs) := if ltr then some (lhs, rhs) else some (rhs, lhs)
| none := none
end

meta def try_sup_pos : tactic clause := do
guard $ clause.literal.is_pos (clause.get_lit c1 i1) ∧ clause.literal.is_pos (clause.get_lit c2 i2),
qf1 ← clause.open_metan c1 (clause.num_quants c1),
qf2 ← clause.open_metan c2 (clause.num_quants c2),
focused1 ← clause.focus qf1↣1 i1,
focused2 ← clause.focus qf2↣1 i2,
opened1 ← clause.open_constn focused1 (focused1↣num_lits - 1),
opened2 ← clause.open_constn focused2 (focused2↣num_lits - 1),
match is_eq_dir opened1↣1↣type ltr with
| none := failed
| (some (rwr_from, rwr_to)) := do
atom ← return opened2↣1↣type,
eq_type ← infer_type rwr_from,
atom_at_pos_type ← infer_type (get_position atom pos),
unify eq_type atom_at_pos_type,
unify rwr_from (get_position atom pos),
rwr_ctx_varn ← mk_fresh_name,
abs_rwr_ctx ← return $
  lam rwr_ctx_varn binder_info.default eq_type (replace_position (mk_var 0) atom pos),
univ ← infer_univ eq_type,
new_fin_prf ←
  return $ app_of_list (const congr_ax [univ]) [eq_type, rwr_from, rwr_to,
            abs_rwr_ctx, opened1↣1↣prf, opened2↣1↣prf],
rwr_from' ← instantiate_mvars rwr_from,
rwr_to' ← instantiate_mvars rwr_to,
guard $ ¬gt rwr_to' rwr_from',
new_fin_type ← infer_type new_fin_prf >>= whnf,
clause.meta_closure (qf1.2 ++ qf2.2) $
  clause.close_constn (clause.mk 0 1 tt new_fin_prf new_fin_type) (opened1.2 ++ opened2.2)
end

example (i : Type) (a b : i) (p : i → Prop) (H : a = b) (Hpa : p a) : true := by do
H ← get_local `H, Hcls ← liftM (clause.mk 0 1 tt H) (infer_type H),
Hpa ← get_local `Hpa, Hpacls ← liftM (clause.mk 0 1 tt Hpa) (infer_type Hpa),
a ← get_local `a,
try_sup_pos (λx y, ff) Hcls Hpacls 0 0 [0] tt ``sup_f_ltr,
to_expr `(trivial) >>= apply

lemma sup_l_ltr {A C} {a1 a2} (f : A → Prop) (H : a1 = a2) : (f a1 → C) → (f a2 → C) := take Hfa1C, H ▸ Hfa1C
lemma sup_l_rtl {A C} {a1 a2} (f : A → Prop) (H : a2 = a1) : (f a1 → C) → (f a2 → C) := sup_l_ltr f H↣symm

meta def try_sup_neg : tactic clause := do
guard $ clause.literal.is_pos (clause.get_lit c1 i1) ∧ clause.literal.is_neg (clause.get_lit c2 i2),
qf1 ← clause.open_metan c1 (clause.num_quants c1),
qf2 ← clause.open_metan c2 (clause.num_quants c2),
focused1 ← clause.focus qf1↣1 i1,
opened1 ← clause.open_constn focused1 (focused1↣num_lits - 1),
opened2 ← clause.open_constn qf2↣1 i2,
match is_eq_dir opened1↣1↣type ltr with
| none := failed
| (some (rwr_from, rwr_to)) := do
atom ← return $ binding_domain opened2↣1↣type,
eq_type ← infer_type rwr_from,
atom_at_pos_type ← infer_type (get_position atom pos),
unify eq_type atom_at_pos_type,
unify rwr_from (get_position atom pos),
rwr_ctx_varn ← mk_fresh_name,
abs_rwr_ctx ← return $
  lam rwr_ctx_varn binder_info.default eq_type (replace_position (mk_var 0) atom pos),
univ ← infer_univ eq_type,
new_fin_prf ← return $ app_of_list (const congr_ax [univ])
  [eq_type, binding_body opened2↣1↣type, rwr_from, rwr_to,
   abs_rwr_ctx, opened1↣1↣prf, opened2↣1↣prf],
rwr_from' ← instantiate_mvars rwr_from,
rwr_to' ← instantiate_mvars rwr_to,
guard $ ¬gt rwr_to' rwr_from',
new_fin_type ← infer_type new_fin_prf,
new_fin_c ← clause.whnf_head_lit { (opened2↣1) with type := new_fin_type, prf := new_fin_prf },
clause.meta_closure (qf1.2 ++ qf2.2) $
  clause.close_constn new_fin_c (opened1.2 ++ opened2.2)
end

example (i : Type) (a b : i) (p : i → Prop) (H : a = b) (Hpa : p a → false) (Hpb : p b → false) : true := by do
H ← get_local `H, Hcls ← liftM (clause.mk 0 1 tt H) (infer_type H),
Hpa ← get_local `Hpa, Hpacls ← liftM (clause.mk 0 1 ff Hpa) (infer_type Hpa),
Hpb ← get_local `Hpb, Hpbcls ← liftM (clause.mk 0 1 ff Hpb) (infer_type Hpb),
try_sup_neg (λx y, ff) Hcls Hpacls 0 0 [0] tt ``sup_l_ltr,
try_sup_neg (λx y, ff) Hcls Hpbcls 0 0 [0] ff ``sup_l_rtl,
to_expr `(trivial) >>= apply

meta def rwr_positions (c : clause) (i : nat) : list (list ℕ) :=
get_rwr_positions (clause.literal.formula (clause.get_lit c i))

meta def try_add_sup_pos : resolution_prover unit :=
(do c' ← resolution_prover_of_tactic $ try_sup_pos gt ac1↣c ac2↣c i1 i2 pos ltr congr_ax, add_inferred c' [ac1,ac2])
    <|> return ()

meta def try_add_sup_neg : resolution_prover unit :=
(do c' ← resolution_prover_of_tactic $ try_sup_neg gt ac1↣c ac2↣c i1 i2 pos ltr congr_ax, add_inferred c' [ac1,ac2])
    <|> return ()

meta def superposition_pos_back_inf : inference :=
take given, do active ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_pos (clause.get_lit given↣c given_i),
  option.to_monad $ is_eq (clause.literal.formula $ clause.get_lit given↣c given_i),
  other ← rb_map.values active,
  other_i ← other↣selected,
  guard $ clause.literal.is_pos (clause.get_lit other↣c other_i),
  pos ← rwr_positions other↣c other_i,
  [do try_add_sup_pos gt given other given_i other_i pos tt ``sup_f_ltr,
      try_add_sup_pos gt given other given_i other_i pos ff ``sup_f_rtl]

meta def superposition_pos_fwd_inf : inference :=
take given, do active ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_pos (clause.get_lit given↣c given_i),
  other ← rb_map.values active,
  other_i ← other↣selected,
  guard $ clause.literal.is_pos (clause.get_lit other↣c other_i),
  option.to_monad $ is_eq (clause.literal.formula $ clause.get_lit other↣c other_i),
  pos ← rwr_positions given↣c given_i,
  [do try_add_sup_pos gt other given other_i given_i pos tt ``sup_f_ltr,
      try_add_sup_pos gt other given other_i given_i pos ff ``sup_f_rtl]

meta def superposition_neg_back_inf : inference :=
take given, do active ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_pos (clause.get_lit given↣c given_i),
  option.to_monad $ is_eq (clause.literal.formula $ clause.get_lit given↣c given_i),
  other ← rb_map.values active,
  other_i ← other↣selected,
  guard $ clause.literal.is_neg (clause.get_lit other↣c other_i),
  pos ← rwr_positions other↣c other_i,
  [do try_add_sup_neg gt given other given_i other_i pos tt ``sup_l_ltr,
      try_add_sup_neg gt given other given_i other_i pos ff ``sup_l_rtl]

meta def superposition_neg_fwd_inf : inference :=
take given, do active ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_neg (clause.get_lit given↣c given_i),
  other ← rb_map.values active,
  other_i ← other↣selected,
  guard $ clause.literal.is_pos (clause.get_lit other↣c other_i),
  option.to_monad $ is_eq (clause.literal.formula $ clause.get_lit other↣c other_i),
  pos ← rwr_positions given↣c given_i,
  [do try_add_sup_neg gt other given other_i given_i pos tt ``sup_l_ltr,
      try_add_sup_neg gt other given other_i given_i pos ff ``sup_l_rtl]

meta def superposition_inf : inference :=
take given, do gt ← get_term_order,
superposition_pos_fwd_inf gt given,
superposition_pos_back_inf gt given,
superposition_neg_fwd_inf gt given,
superposition_neg_back_inf gt given
