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
  hyp_opt ← get_sat_hyp_core hd↣formula hd↣is_pos,
  match hyp_opt with
  | some h :=
    if hd↣is_final then do
      c' ← resolution_prover_of_tactic c↣fin_to_pos,
      extract_assertions (c↣inst h)
    else do
      extract_assertions (c↣inst h)
  | _ := do
    op ← resolution_prover_of_tactic c↣open_const,
    op_wo_as ← extract_assertions op↣1,
    return (op_wo_as↣1↣close_const op↣2, op_wo_as↣2)
  end

meta def splitting_inf : inference := take given,
if given↣c↣num_quants ≠ 0 ∨ given↣c↣num_lits ≤ 1 then
  return ()
else do
  add_sat_clause given↣c,
  remove_redundant given↣id []
