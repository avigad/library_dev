import prover_state
open monad

meta def extract_assertions : cls → resolution_prover (cls × list expr) | c :=
if c↣num_lits = 0 then return (c, [])
else if c↣num_quants ≠ 0 then do
  qf ← resolution_prover_of_tactic $ c↣open_constn c↣num_quants,
  qf_wo_as ← extract_assertions qf↣1,
  return (qf_wo_as↣1↣close_constn qf↣2, qf_wo_as↣2)
else do
  hd ← return $ c↣get_lit 0,
  hyp_opt ← get_sat_hyp_core hd↣formula hd↣is_neg,
  match hyp_opt with
  | some h :=
    if hd↣is_final then do
      c' ← resolution_prover_of_tactic c↣fin_to_pos,
      return (c'↣inst h, [h])
    else do
      wo_as ← extract_assertions (c↣inst h),
      return (wo_as↣1, h :: wo_as↣2)
  | _ :=
    if hd↣is_final then
      return (c, [])
    else do
      op ← resolution_prover_of_tactic c↣open_const,
      op_wo_as ← extract_assertions op↣1,
      return (op_wo_as↣1↣close_const op↣2, op_wo_as↣2)
  end

meta def splitting_inf : inference := take given,
if given↣c↣num_lits ≤ 1 then return () else do
forM given↣c↣get_lits (λl,
     if l↣formula↣has_var ∨ l↣formula↣is_not↣is_some then
       return ()
     else
       mk_sat_var l↣formula l↣is_neg),
with_ass ← extract_assertions given↣c,
if with_ass↣2↣length > 0 then do
  add_inferred with_ass↣1 [given],
  remove_redundant given↣id []
else
  return ()

meta def splitting_pre : resolution_prover unit :=
preprocessing_rule $ take news, do flip filterM news $ take new, do
ass ← collect_ass_hyps new,
if new↣num_quants = 0 ∧ new↣num_lits > 1 then do
  add_sat_clause $ new↣close_constn ass,
  return ff
else if new↣num_quants = 0 ∧ new↣num_lits = 1 then do
  hd ← return $ new↣get_lit 0,
  hyp ← get_sat_hyp_core hd↣formula hd↣is_neg,
  if hyp↣is_some then do
    add_sat_clause $ new↣close_constn ass,
    return ff
  else
    return tt
else
  return tt
