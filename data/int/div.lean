import algebra.ring

namespace int

lemma coe_nat_dvd_coe_nat_of_dvd {m n : ℕ} (h : m ∣ n) : (↑m : ℤ) ∣ ↑n :=
dvd.elim h $ λk e, dvd.intro k $ by rw [e, int.coe_nat_mul]

lemma dvd_of_coe_nat_dvd_coe_nat {m n : ℕ} (h : (↑m : ℤ) ∣ ↑n) : m ∣ n :=
dvd.elim h $ λa ae,
  m.eq_zero_or_pos.elim
  (λm0, by rw[m0, int.coe_nat_zero, zero_mul] at ae;
           rw [int.coe_nat_inj ae]; apply dvd_zero)
  (λm0l, let ⟨k, ke⟩ := int.eq_coe_of_zero_le $ nonneg_of_mul_nonneg_left
      (by rw -ae; apply int.coe_zero_le : 0 ≤ (m:ℤ) * a)
      (int.coe_nat_le_coe_nat_of_le m0l) in
    by rw [ke, -int.coe_nat_mul] at ae; exact dvd.intro _ (int.coe_nat_inj ae).symm)

lemma coe_nat_dvd_coe_nat_iff (m n : ℕ) : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
⟨dvd_of_coe_nat_dvd_coe_nat, coe_nat_dvd_coe_nat_of_dvd⟩

end int
