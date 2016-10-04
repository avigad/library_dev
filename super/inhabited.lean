import .clause_ops .prover_state
open expr tactic monad

namespace super

meta def try_nonempty_lookup_left (c : clause) : tactic (list clause) :=
on_first_left_dn c $ λhnx,
  match is_not hnx↣local_type with
  | some type := do
    univ ← infer_univ type,
    inst ← mk_instance (app (const ``nonempty [univ]) type),
    instt ← infer_type inst,
    trace [hnx, hnx↣local_type, type, inst, instt],
    return [([], app_of_list (const ``nonempty.elim [univ])
                             [type, false_, inst, hnx])]
  | _ := failed
  end

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

meta def inhabited_infs : inference := take given, do
forM' [try_nonempty_lookup_left,
       try_nonempty_left, try_nonempty_right,
       try_inhabited_left, try_inhabited_right] $ λr,
      simp_if_successful given (r given↣c)

end super
