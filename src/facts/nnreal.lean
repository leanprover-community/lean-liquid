import data.real.nnreal

open_locale nnreal

namespace nnreal

variables (r' k c c₁ c₂ c₃ : ℝ≥0)

instance fact_le_mul_of_one_le_left [hk : fact (1 ≤ k)] [hc : fact (c₁ ≤ c₂)] :
  fact (c₁ ≤ k * c₂) :=
calc c₁ = 1 * c₁ : (one_mul _).symm
    ... ≤ k * c₂ : mul_le_mul' hk hc

instance fact_mul_le_of_le_one_left [hk : fact (k ≤ 1)] [hc : fact (c₁ ≤ c₂)] :
  fact (k * c₁ ≤ c₂) :=
calc k * c₁ ≤ 1 * c₂ : mul_le_mul' hk hc
        ... = c₂     : one_mul _

instance fact_le_refl : fact (c ≤ c) := le_rfl

instance fact_le_subst_right [fact (c₁ ≤ c₂)] [h : fact (c₂ = c₃)]: fact (c₁ ≤ c₃) :=
by rwa ← show c₂ = c₃, from h

instance fact_le_subst_right' [fact (c₁ ≤ c₂)] [h : fact (c₃ = c₂)]: fact (c₁ ≤ c₃) :=
by rwa ← show c₂ = c₃, from h.symm

instance fact_le_subst_left [fact (c₁ ≤ c₂)] [h : fact (c₁ = c₃)]: fact (c₃ ≤ c₂) :=
by rwa ← show c₁ = c₃, from h

instance fact_le_subst_left' [fact (c₁ ≤ c₂)] [h : fact (c₃ = c₁)]: fact (c₃ ≤ c₂) :=
by rwa ← show c₁ = c₃, from h.symm

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

instance fact_le_max_left (a b c : ℝ≥0) [h : fact (a ≤ b)] : fact (a ≤ max b c) :=
le_trans h $ le_max_left _ _

instance fact_one_le_mul_self (a : ℝ≥0) [h : fact (1 ≤ a)] : fact (1 ≤ a * a) :=
calc (1 : ℝ≥0) = 1 * 1 : (mul_one 1).symm
           ... ≤ a * a : mul_le_mul' h h

instance one_le_add {a b : ℝ≥0} [ha : fact (1 ≤ a)] : fact (1 ≤ a + b) := le_trans ha $ by simp
instance one_le_add' {a b : ℝ≥0} [hb : fact (1 ≤ b)] : fact (1 ≤ a + b) := le_trans hb $ by simp

instance one_le_pow {n : ℕ} {a : ℝ≥0} [h : fact (1 ≤ a)] : fact (1 ≤ a^n) :=
begin
  cases n,
  { simp [le_refl] },
  { rwa one_le_pow_iff,
    apply nat.succ_ne_zero }
end

instance fact_le_mul_add : fact (c * c₁ + c * c₂ ≤ c * (c₁ + c₂)) :=
by { rw mul_add, exact le_rfl }

end nnreal
#lint- only unused_arguments def_lemma doc_blame
