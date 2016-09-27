import prover_state
open monad

meta def splitting_inf : inference := take given,
if given↣c↣num_quants ≠ 0 ∨ given↣c↣num_lits - given↣assertions↣length ≤ 1 then
   return ()
else do
  add_sat_clause given↣c,
  remove_redundant given↣id []
