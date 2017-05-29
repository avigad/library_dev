import algebra.ring
import init.data.nat.basic
namespace nat

protected theorem dvd_add_iff_right {k m n : ℕ} (h : k ∣ m) : k ∣ n ↔ k ∣ m + n :=
⟨dvd_add h, dvd.elim h $ λd hd, match m, hd with
| ._, rfl := λh₂, dvd.elim h₂ $ λe he, ⟨e - d,
  by rw [nat.mul_sub_left_distrib, -he, nat.add_sub_cancel_left]⟩
end⟩

protected theorem dvd_add_iff_left {k m n : ℕ} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n :=
by rw add_comm; exact nat.dvd_add_iff_right h

theorem dvd_sub {k m n : ℕ} (H : n ≤ m) (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
(nat.dvd_add_iff_left h₂).2 $ by rw nat.sub_add_cancel H; exact h₁

theorem dvd_mod_iff {k m n : ℕ} (h : k ∣ n) : k ∣ m % n ↔ k ∣ m :=
let t := @nat.dvd_add_iff_left _ (m % n) _ (dvd_trans h (dvd_mul_right n (m / n))) in
by rwa mod_add_div at t

lemma le_of_dvd {m n : ℕ} (h : n > 0) : m ∣ n → m ≤ n :=
λ⟨k, e⟩, by {
  revert h, rw e, refine k.cases_on _ _,
  exact λhn, absurd hn (lt_irrefl _),
  exact λk _, let t := mul_le_mul_left m (succ_pos k) in by rwa mul_one at t }

theorem dvd.antisymm : Π {m n : ℕ}, m ∣ n → n ∣ m → m = n
| m        0        h₁ h₂ := eq_zero_of_zero_dvd h₂
| 0        n        h₁ h₂ := (eq_zero_of_zero_dvd h₁).symm
| (succ m) (succ n) h₁ h₂ := le_antisymm (le_of_dvd (succ_pos _) h₁) (le_of_dvd (succ_pos _) h₂)

theorem pos_of_dvd_of_pos {m n : ℕ} (H1 : m ∣ n) (H2 : n > 0) : m > 0 :=
nat.pos_of_ne_zero $ λm0, by rw m0 at H1; rw eq_zero_of_zero_dvd H1 at H2; exact lt_irrefl _ H2

theorem eq_one_of_dvd_one {n : ℕ} (H : n ∣ 1) : n = 1 :=
le_antisymm (le_of_dvd dec_trivial H) (pos_of_dvd_of_pos H dec_trivial)

theorem dvd_of_mod_eq_zero {m n : ℕ} (H : n % m = 0) : m ∣ n :=
dvd.intro (n / m) $ let t := mod_add_div n m in by simp [H] at t; exact t

theorem mod_eq_zero_of_dvd {m n : ℕ} (H : m ∣ n) : n % m = 0 :=
dvd.elim H (λ z H1, by rw [H1, mul_mod_right])

theorem dvd_iff_mod_eq_zero (m n : ℕ) : m ∣ n ↔ n % m = 0 :=
⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

instance decidable_dvd : decidable_rel (@has_dvd.dvd nat _) :=
λm n, decidable_of_decidable_of_iff (by apply_instance) (dvd_iff_mod_eq_zero _ _).symm

protected theorem mul_div_cancel' {m n : ℕ} (H : n ∣ m) : n * (m / n) = m :=
let t := mod_add_div m n in by rwa [mod_eq_zero_of_dvd H, zero_add] at t

protected theorem div_mul_cancel {m n : ℕ} (H : n ∣ m) : m / n * n = m :=
by rw [mul_comm, nat.mul_div_cancel' H]

protected theorem mul_div_assoc (m : ℕ) {n k : ℕ} (H : k ∣ n) : m * n / k = m * (n / k) :=
or.elim (eq_zero_or_pos k)
  (λh, by rw [h, nat.div_zero, nat.div_zero, mul_zero])
  (λh, have m * n / k = m * (n / k * k) / k, by rw nat.div_mul_cancel H,
       by rw[this, -mul_assoc, nat.mul_div_cancel _ h])

theorem dvd_of_mul_dvd_mul_left {m n k : ℕ} (kpos : k > 0) (H : k * m ∣ k * n) : m ∣ n :=
dvd.elim H (λl H1, by rw mul_assoc at H1; exact ⟨_, eq_of_mul_eq_mul_left kpos H1⟩)

theorem dvd_of_mul_dvd_mul_right {m n k : ℕ} (kpos : k > 0) (H : m * k ∣ n * k) : m ∣ n :=
by rw [mul_comm m k, mul_comm n k] at H; exact dvd_of_mul_dvd_mul_left kpos H

end nat
