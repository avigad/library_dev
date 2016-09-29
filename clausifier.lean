import clause clause_ops
import prover_state
open expr list tactic monad decidable

meta def try_option {a} (tac : tactic a) : tactic (option a) :=
liftM some tac <|> return none

private meta def on_first_right (c : clause)
        (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c↣num_lits, [on_right_at c i f]

private meta def on_first_right' (c : clause)
        (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c↣num_lits, [on_right_at' c i f]

private meta def on_first_left (c : clause)
        (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c↣num_lits, [on_left_at c i f]

meta def inf_whnf_l (c : clause) : tactic (list clause) :=
on_first_left c $ λtype, do
  type' ← whnf type,
  guard $ type' ≠ type,
  h ← mk_local_def `h type',
  return [([h], h)]

meta def inf_whnf_r (c : clause) : tactic (list clause) :=
on_first_right c $ λha, do
  a' ← whnf ha↣local_type,
  guard $ a' ≠ ha↣local_type,
  hna ← mk_local_def `hna (imp a' false_),
  return [([hna], app hna ha)]

set_option eqn_compiler.max_steps 500

meta def inf_false_l (c : clause) : tactic (list clause) :=
first $ do i ← list.range c↣num_lits,
  if c↣get_lit 0 = clause.literal.left (const ``false [])
  then [return []]
  else []

meta def inf_false_r (c : clause) : tactic (list clause) :=
on_first_right c $ λhf,
  match hf↣local_type with
  | (const ``false []) := return [([], hf)]
  | _ := failed
  end

meta def inf_true_l (c : clause) : tactic (list clause) :=
on_first_left c $ λt,
  match t with
  | (const ``true []) := return [([], const ``true.intro [])]
  | _ := failed
  end

meta def inf_true_r (c : clause) : tactic (list clause) :=
first $ do i ← list.range c↣num_lits,
  if c↣get_lit i = clause.literal.right (const ``true [])
  then [return []]
  else []

meta def inf_not_r (c : clause) : tactic (list clause) :=
on_first_right c $ λhna,
  match is_not hna↣local_type with
  | some a := do
    ha ← mk_local_def `h a,
    return [([ha], app hna ha)]
  | _ := failed
  end

meta def inf_and_l (c : clause) : tactic (list clause) :=
on_first_left c $ λab,
  match ab with
  | (app (app (const ``and []) a) b) := do
    ha ← mk_local_def `l a,
    hb ← mk_local_def `r b,
    pab ← mk_mapp ``and.intro [some a, some b, some ha, some hb],
    return [([ha, hb], pab)]
  | _ := failed
  end

meta def inf_and_r (c : clause) : tactic (list clause) :=
on_first_right' c $ λhyp, do
  pa ← mk_mapp ``and.left [none, none, some hyp],
  pb ← mk_mapp ``and.right [none, none, some hyp],
  return [([], pa), ([], pb)]

meta def inf_or_r (c : clause) : tactic (list clause) :=
on_first_right c $ λhab,
  match hab↣local_type with
  | (app (app (const ``or []) a) b) := do
    hna ← mk_local_def `l (not_ a),
    hnb ← mk_local_def `r (not_ b),
    proof ← mk_mapp ``or.elim [some a, some b, some false_, some hab, some hna, some hnb],
    return [([hna, hnb], proof)]
  | _ := failed
  end

meta def inf_or_l (c : clause) : tactic (list clause) :=
on_first_left c $ λab,
  match ab with
  | (app (app (const ``or []) a) b) := do
    ha ← mk_local_def `l a,
    hb ← mk_local_def `l b,
    pa ← mk_mapp ``or.inl [some a, some b, some ha],
    pb ← mk_mapp ``or.inr [some a, some b, some hb],
    return [([ha], pa), ([hb], pb)]
  | _ := failed
  end

meta def inf_all_r (c : clause) : tactic (list clause) :=
on_first_right' c $ λhallb,
  match hallb↣local_type with
  | (pi n bi a b) := do
    ha ← mk_local_def `x a,
    return [([ha], app hallb ha)]
  | _ := failed
  end

lemma imp_of_neg {a b} : (a → false) → (a → b) := take hna ha, false.rec _ (hna ha)
meta def inf_imp_l (c : clause) : tactic (list clause) :=
on_first_left c $ λab,
  match ab with
  | (pi _ _ a b) :=
    if b↣has_var then failed else do
    hna ← mk_local_def `na (imp a false_),
    pna ← mk_mapp ``imp_of_neg [some a, some b, some hna],
    hb ← mk_local_def `b b,
    return [([hna], pna), ([hb], lam `a binder_info.default a hb)]
  | _ := failed
  end

meta def inf_ex_l (c : clause) : tactic (list clause) :=
on_first_left c $ λexp,
  match exp with
  | (app (app (const ``Exists [u]) dom) pred) := do
    hx ← mk_local_def `x dom,
    predx ← whnf $ app pred hx,
    hpx ← mk_local_def `hpx predx,
    return [([hx,hpx], app_of_list (const ``exists.intro [u])
                       [dom, pred, hx, hpx])]
  | _ := failed
  end

lemma demorgan {a} {b : a → Prop} : (¬∃x:a, ¬b x) → ∀x, b x :=
take nenb x, classical.by_contradiction (take nbx, nenb (exists.intro x nbx))

meta def inf_all_l (c : clause) : tactic (list clause) :=
on_first_left c $ λallb,
  match allb with
  | (pi n bi a b) := do
    enb ← mk_mapp ``Exists [none, some $ lam n binder_info.default a (not_ b)],
    hnenb ← mk_local_def `h (not_ enb),
    pallb ← mk_mapp ``demorgan [some a, none, some hnenb],
    return [([hnenb], pallb)]
  | _ := failed
  end

meta def inf_ex_r  (c : clause) : tactic (list clause) := do
(qf, ctx) ← c↣open_constn c↣num_quants,
skolemized ← on_first_right' qf $ λhexp,
  match hexp↣local_type with
  | (app (app (const ``Exists [u]) d) p) := do
    sk_sym_name_pp ← get_unused_name `sk (some 1),
    inh_lc ← mk_local `w binder_info.implicit d,
    sk_sym ← mk_local_def sk_sym_name_pp (pis (ctx ++ [inh_lc]) d),
    sk_p ← whnf_core transparency.none $ app p (app_of_list sk_sym (ctx ++ [inh_lc])),
    sk_ax ← mk_mapp ``Exists [some (local_type sk_sym),
      some (lambdas [sk_sym] (pis (ctx ++ [inh_lc]) (imp hexp↣local_type sk_p)))],
    sk_ax_name ← get_unused_name `sk_axiom (some 1), assert sk_ax_name sk_ax,
    nonempt_of_inh ← mk_mapp ``nonempty.intro [some d, some inh_lc],
    eps ← mk_mapp ``classical.epsilon [some d, some nonempt_of_inh, some p],
    existsi (lambdas (ctx ++ [inh_lc]) eps),
    eps_spec ← mk_mapp ``classical.epsilon_spec [some d, some p],
    exact (lambdas (ctx ++ [inh_lc]) eps_spec),
    sk_ax_local ← get_local sk_ax_name, cases_using sk_ax_local [sk_sym_name_pp, sk_ax_name],
    sk_ax' ← get_local sk_ax_name,
    return [([inh_lc], app_of_list sk_ax' (ctx ++ [inh_lc, hexp]))]
  | _ := failed
  end,
return $ skolemized↣for (λs, s↣close_constn ctx)

meta def first_some {a : Type} : list (tactic (option a)) → tactic (option a)
| [] := return none
| (x::xs) := do xres ← x, match xres with some y := return (some y) | none := first_some xs end

meta def clausification_rules  : list (clause → tactic (list clause)) :=
[ inf_false_l, inf_false_r, inf_true_l, inf_true_r,
  inf_not_r,
  inf_and_l, inf_and_r,
  inf_or_l, inf_or_r,
  inf_imp_l, inf_all_r,
  inf_ex_l,
  inf_all_l, inf_ex_r,
  inf_whnf_l, inf_whnf_r ]

meta def clausify : list clause → tactic (list clause) | cs :=
liftM list.join $ do
forM cs $ λc, do first $
clausification_rules↣for (λr, r c >>= clausify) ++ [return [c]]

meta def clausification_pre : resolution_prover unit :=
preprocessing_rule $ λnew, ↑(clausify new)

meta def clausification_inf : inference :=
λgiven, list.foldr orelse (return ()) $
        do r ← clausification_rules,
           [do cs ← ↑(r given↣c),
               cs' ← ↑(clausify cs),
               forM' cs' (λc, add_inferred c [given]),
               remove_redundant given↣id []]
