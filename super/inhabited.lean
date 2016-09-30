import clause_ops prover_state
open expr tactic monad

meta def nonempty_lookup_left (c : clause) : tactic (list clause) :=
collect_successes $ do l ← c↣get_lits, guard l↣is_neg, return $ do
  type ← return l↣formula,
  guard ¬type↣has_var,
  univ ← infer_univ type,
  inst ← mk_instance (app (const ``nonempty [univ]) type),
  clause.of_proof inst

meta def try_nonempty_left (c : clause) : tactic (list clause) :=
on_first_left c $ λprop,
  match prop with
  | (app (const ``nonempty [u]) type) := do
    x ← mk_local_def `x type,
    return [([x], app_of_list (const ``nonempty.intro [u]) [type, x])]
  | _ := failed
  end

meta def try_nonempty_right (c : clause) : tactic (list clause) :=
on_first_right c $ λhnonempty,
  match hnonempty↣local_type with
  | (app (const ``nonempty [u]) type) := do
    hnx ← mk_local_def `nx (imp type false_),
    return [([hnx], app_of_list (const ``nonempty.elim [u])
                                [type, false_, hnonempty, hnx])]
  | _ := failed
  end

meta def try_inhabited_left (c : clause) : tactic (list clause) :=
on_first_left c $ λprop,
  match prop with
  | (app (const ``inhabited [u]) type) := do
    x ← mk_local_def `x type,
    return [([x], app_of_list (const ``inhabited.mk [u]) [type, x])]
  | _ := failed
  end

meta def try_inhabited_right (c : clause) : tactic (list clause) :=
on_first_right' c $ λhinh,
  match hinh↣local_type with
  | (app (const ``inhabited [u]) type) :=
    return [([], app_of_list (const ``inhabited.default [u]) [type, hinh])]
  | _ := failed
  end

meta def simp_if_successful (parent : active_cls) (tac : tactic (list clause)) : resolution_prover unit :=
(do inferred ← ↑tac, forM' inferred $ λc, add_inferred c [parent], remove_redundant parent↣id [])
<|> return ()

meta def inhabited_infs : inference := take given, do
insts ← ↑(nonempty_lookup_left given↣c),
forM' insts (λc, add_inferred c []),
forM' [try_nonempty_left, try_nonempty_right, try_inhabited_left, try_inhabited_right] $ λr,
      simp_if_successful given (r given↣c)
