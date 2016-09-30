import prover
open tactic

set_option trace.resolution true

lemma even_gapt_can_do_that {A B} {p : A → B → Prop} {f : A → B} {g : (A → B) → A} :
  ∃x y, p x (f x) → p (g y) (y (g y)) := by do
repeat $ mk_mvar >>= existsi,
intro1 >>= apply

example (A B : Type) (p : A → B → Prop) (a : A) (b : B) :
  (∀x, ∃y, p x y) → ∃f : A → B, ∀x, p x (f x) := by prover_tactic
