import .prover_state
open monad expr list tactic

namespace super

private meta def find_components : list expr → list (list (expr × ℕ)) → list (list (expr × ℕ))
| (e::es) comps :=
  let (contain_e, do_not_contain_e) :=
      partition (λc : list (expr × ℕ), c↣exists_ $ λf,
        (abstract_local f↣1 e↣local_uniq_name)↣has_var) comps in
    find_components es $ list.join contain_e :: do_not_contain_e
| _ comps := comps

meta def get_components (hs : list expr) : list (list expr) :=
(find_components hs (hs↣zip_with_index↣for $ λh, [h]))↣for $ λc,
(sort_on (λh : expr × ℕ, h↣2) c)↣for $ λh, h↣1

example (i : Type) (p q : i → Prop) (H : ∀x y, p x → q y → false) : true := by do
h ← get_local `H >>= clause.of_proof,
(op, lcs) ← h↣open_constn h↣num_binders,
guard $ (get_components lcs)↣length = 2,
triv

example (i : Type) (p : i → i → Prop) (H : ∀x y z, p x y → p y z → false) : true := by do
h ← get_local `H >>= clause.of_proof,
(op, lcs) ← h↣open_constn h↣num_binders,
guard $ (get_components lcs)↣length = 1,
triv

meta def extract_assertions : clause → resolution_prover (clause × list expr) | c :=
if c↣num_lits = 0 then return (c, [])
else if c↣num_quants ≠ 0 then do
  qf : clause × list expr ← ↑(c↣open_constn c↣num_quants),
  qf_wo_as ← extract_assertions qf↣1,
  return (qf_wo_as↣1↣close_constn qf↣2, qf_wo_as↣2)
else do
  hd ← return $ c↣get_lit 0,
  hyp_opt ← get_sat_hyp_core hd↣formula hd↣is_neg,
  match hyp_opt with
  | some h := do
      wo_as ← extract_assertions (c↣inst h),
      return (wo_as↣1, h :: wo_as↣2)
  | _ := do
      op : clause × expr ← ↑c↣open_const,
      op_wo_as ← extract_assertions op↣1,
      return (op_wo_as↣1↣close_const op↣2, op_wo_as↣2)
  end

meta def mk_splitting_clause' (orig_proof : expr) : list (list expr) → tactic (list expr × expr)
| [] := return ([], orig_proof)
| ([p] :: comps) := do p' : list expr × expr ← mk_splitting_clause' comps, return (p::p'↣1, p'↣2)
| (comp :: comps) := do
  (hs, p') ← mk_splitting_clause' comps,
  hnc ← mk_local_def `hnc (pis comp false_)↣not_,
  p'' ← return $ app hnc (lambdas comp p'),
  return (hnc::hs, p'')

meta def mk_splitting_clause (orig_proof : expr) (comps : list (list expr)) : tactic clause := do
(hs, p) ← mk_splitting_clause' orig_proof comps,
return $ (clause.mk 0 0 p false_)↣close_constn hs

meta def splitting_inf : inference := take given, do
op : clause × list expr ← ↑(given↣c↣open_constn given↣c↣num_binders),
if list.bor (given↣c↣get_lits↣for $ λl, l↣formula↣is_not↣is_some) then return () else
let comps := get_components op↣2 in
if comps↣length < 2 then return () else do
splitting_clause ← ↑(mk_splitting_clause op↣1↣proof comps),
ass ← collect_ass_hyps splitting_clause,
add_sat_clause $ splitting_clause↣close_constn ass,
remove_redundant given↣id []

end super
