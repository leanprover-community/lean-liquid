import data.real.nnreal

open_locale nnreal

namespace nnreal

variables (r' k c c₁ c₂ : ℝ≥0)

instance fact_le_mul_of_one_le_left [hk : fact (1 ≤ k)] : fact (c ≤ k * c) :=
le_mul_of_one_le_left c.2 hk

instance fact_le_refl : fact (c ≤ c) := le_rfl

instance fact_mul_le_mul_left [fact (c₁ ≤ c₂)] : fact (r' * c₁ ≤ r' * c₂) := mul_le_mul' le_rfl ‹_›

instance fact_mul_le_mul_right [fact (c₁ ≤ c₂)] : fact (c₁ * r' ≤ c₂ * r') := mul_le_mul' ‹_› le_rfl

instance fact_le_inv_mul_self [h1 : fact (0 < r')] [h2 : fact (r' ≤ 1)] : fact (c ≤ r'⁻¹ * c) :=
begin
  rw mul_comm,
  apply le_mul_inv_of_mul_le (ne_of_gt h1),
  nth_rewrite 1 ← mul_one c,
  exact mul_le_mul (le_of_eq rfl) h2 (le_of_lt h1) zero_le',
end

end nnreal
#lint- only unused_arguments
