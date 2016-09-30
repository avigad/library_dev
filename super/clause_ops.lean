import clause
open monad tactic expr

meta def on_left_at {m} [monad m] (c : clause) (i : ℕ)
                    [has_coe_fam tactic m]
                    -- f gets a type and returns a list of proofs of that type
                    (f : expr → m (list (list expr × expr))) : m (list clause) := do
op : clause × list expr ← ↑(c↣open_constn (c↣num_quants + i)),
() : unit ← ↑(@guard tactic _ ((op↣1↣get_lit 0)↣is_neg) _),
new_hyps ← f (op↣1↣get_lit 0)↣formula,
return $ new_hyps↣for (λnew_hyp,
  (op↣1↣inst new_hyp↣2)↣close_constn (op↣2 ++ new_hyp↣1))

meta def on_right_at {m} [monad m] (c : clause) (i : ℕ)
                     [has_coe_fam tactic m]
                     -- f gets a hypothesis and returns a list of proofs of false
                     (f : expr → m (list (list expr × expr))) : m (list clause) := do
op : clause × list expr ← ↑(c↣open_constn (c↣num_quants + i)),
() : unit ← ↑(@guard tactic _ ((op↣1↣get_lit 0)↣is_pos) _),
hn ← ↑mk_fresh_name,
h ← return $ local_const hn `h binder_info.default (op↣1↣get_lit 0)↣formula,
new_hyps ← f h,
return $ new_hyps↣for (λnew_hyp,
  (op↣1↣inst (lambdas [h] new_hyp↣2))↣close_constn (op↣2 ++ new_hyp↣1))

meta def on_right_at' {m} [monad m] (c : clause) (i : ℕ)
                     [has_coe_fam tactic m]
                     -- f gets a hypothesis and returns a list of proofs
                     (f : expr → m (list (list expr × expr))) : m (list clause) := do
op : clause × list expr ← ↑(c↣open_constn (c↣num_quants + i)),
() : unit ← ↑(@guard tactic _ ((op↣1↣get_lit 0)↣is_pos) _),
hn ← ↑mk_fresh_name,
h ← return $ local_const hn `h binder_info.default (op↣1↣get_lit 0)↣formula,
new_hyps ← f h,
forM new_hyps (λnew_hyp, do
  type ← ↑(infer_type new_hyp↣2),
  nhn ← ↑mk_fresh_name,
  nh ← return $ local_const nhn `nh binder_info.default (imp type false_),
  return $ (op↣1↣inst (lambdas [h] (app nh new_hyp↣2)))↣close_constn (op↣2 ++ new_hyp↣1 ++ [nh]))

meta def on_first_right (c : clause) (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c↣num_lits, [on_right_at c i f]

meta def on_first_right' (c : clause) (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c↣num_lits, [on_right_at' c i f]

meta def on_first_left (c : clause) (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c↣num_lits, [on_left_at c i f]
