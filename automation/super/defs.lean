import .clause_ops .prover_state
open tactic expr monad

namespace super

-- FIXME: how to cleanly unfold one level of definitions?
-- what should one level even be? consider dvd->has_dvd->nat_has_dvd->...
meta def try_unfold_one_def (type : expr) : tactic expr := do
whnf type

meta def try_unfold_def_left (c : clause) (i : ℕ) : tactic (list clause) :=
on_left_at c i $ λt, do
  t' ← try_unfold_one_def t,
  ht' ← mk_local_def `h t',
  return [([ht'], ht')]

meta def try_unfold_def_right (c : clause) (i : ℕ) : tactic (list clause) :=
on_right_at c i $ λh, do
  t' ← try_unfold_one_def h↣local_type,
  hnt' ← mk_local_def `h (imp t' c↣local_false),
  return [([hnt'], app hnt' h)]

meta def unfold_def_inf : inference := take given, sequence' $ do
r ← [try_unfold_def_right, try_unfold_def_left],
i ← given↣selected,
[inf_if_successful given (r given↣c i)]

end super
