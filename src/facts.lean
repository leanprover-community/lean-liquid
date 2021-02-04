import data.real.nnreal

open_locale nnreal

namespace nnreal

variables (r' k c c₁ c₂ : ℝ≥0)

instance fact_le_mul_of_one_le_left [hk : fact (1 ≤ k)] : fact (c ≤ k * c) :=
le_mul_of_one_le_left c.2 hk

instance fact_le_refl : fact (c ≤ c) := le_rfl

instance fact_inv_mul_le [h : fact (0 < r')] : fact (r'⁻¹ * (r' * c) ≤ c) :=
le_of_eq $ inv_mul_cancel_left' (ne_of_gt h) _

instance fact_mul_le_mul_left [fact (c₁ ≤ c₂)] : fact (r' * c₁ ≤ r' * c₂) := mul_le_mul' le_rfl ‹_›

instance fact_mul_le_mul_right [fact (c₁ ≤ c₂)] : fact (c₁ * r' ≤ c₂ * r') := mul_le_mul' ‹_› le_rfl

instance fact_le_inv_mul_self [h1 : fact (0 < r')] [h2 : fact (r' ≤ 1)] : fact (c ≤ r'⁻¹ * c) :=
begin
  rw mul_comm,
  apply le_mul_inv_of_mul_le (ne_of_gt h1),
  nth_rewrite 1 ← mul_one c,
  exact mul_le_mul (le_of_eq rfl) h2 (le_of_lt h1) zero_le',
end

instance one_le_add {a b : ℝ≥0} [ha : fact (1 ≤ a)] : fact (1 ≤ a + b) := le_trans ha $ by simp
instance one_le_add' {a b : ℝ≥0} [hb : fact (1 ≤ b)] : fact (1 ≤ a + b) := le_trans hb $ by simp

instance one_le_pow {n : ℕ} {a : ℝ≥0} [h : fact (1 ≤ a)] : fact (1 ≤ a^n) :=
begin
  cases n,
  { simp [le_refl] },
  { rwa one_le_pow_iff,
    apply nat.succ_ne_zero }
end

end nnreal
#lint- only unused_arguments def_lemma doc_blame
