import data.real.nnreal

open_locale nnreal

namespace nnreal

variables (r' k c c₁ c₂ c₃ : ℝ≥0)

instance fact_pos_of_one_le [hk : fact (1 ≤ c)] : fact (0 < c) :=
⟨lt_of_lt_of_le zero_lt_one hk.out⟩

instance fact_le_mul_of_one_le_left [hk : fact (1 ≤ k)] [hc : fact (c₁ ≤ c₂)] :
  fact (c₁ ≤ k * c₂) :=
⟨calc c₁ = 1 * c₁ : (one_mul _).symm
    ... ≤ k * c₂ : mul_le_mul' hk.out hc.out⟩

instance fact_le_mul_of_one_le_right [hc : fact (c₁ ≤ c₂)] [hk : fact (1 ≤ k)] :
  fact (c₁ ≤ c₂ * k) :=
⟨calc c₁ = c₁ * 1 : (mul_one _).symm
    ... ≤ c₂ * k : mul_le_mul' hc.out hk.out⟩

instance fact_mul_le_of_le_one_left [hk : fact (k ≤ 1)] [hc : fact (c₁ ≤ c₂)] :
  fact (k * c₁ ≤ c₂) :=
⟨calc k * c₁ ≤ 1 * c₂ : mul_le_mul' hk.out hc.out
        ... = c₂     : one_mul _⟩

instance fact_one_le_add_one : fact (1 ≤ k + 1) :=
⟨self_le_add_left 1 k⟩

instance fact_le_refl : fact (c ≤ c) := ⟨le_rfl⟩

instance fact_le_subst_right [fact (c₁ ≤ c₂)] [h : fact (c₂ = c₃)]: fact (c₁ ≤ c₃) :=
by rwa ← h.out

instance fact_le_subst_right' [fact (c₁ ≤ c₂)] [h : fact (c₃ = c₂)]: fact (c₁ ≤ c₃) :=
by rwa ← h.out.symm

instance fact_le_subst_left [fact (c₁ ≤ c₂)] [h : fact (c₁ = c₃)]: fact (c₃ ≤ c₂) :=
by rwa ← h.out

instance fact_le_subst_left' [fact (c₁ ≤ c₂)] [h : fact (c₃ = c₁)]: fact (c₃ ≤ c₂) :=
by rwa ← h.out.symm

instance fact_inv_mul_le [h : fact (0 < r')] : fact (r'⁻¹ * (r' * c) ≤ c) :=
⟨le_of_eq $ inv_mul_cancel_left' (ne_of_gt h.out) _⟩

instance fact_mul_le_mul_left [h : fact (c₁ ≤ c₂)] : fact (r' * c₁ ≤ r' * c₂) :=
⟨mul_le_mul' le_rfl h.out⟩

instance fact_mul_le_mul_right [h : fact (c₁ ≤ c₂)] : fact (c₁ * r' ≤ c₂ * r') :=
⟨mul_le_mul' h.out le_rfl⟩

instance fact_le_inv_mul_self [h1 : fact (0 < r')] [h2 : fact (r' ≤ 1)] : fact (c ≤ r'⁻¹ * c) :=
begin
  constructor,
  rw mul_comm,
  apply le_mul_inv_of_mul_le (ne_of_gt h1.out),
  nth_rewrite 1 ← mul_one c,
  exact mul_le_mul (le_of_eq rfl) h2.out (le_of_lt h1.out) zero_le',
end

instance fact_le_max_left (a b c : ℝ≥0) [h : fact (a ≤ b)] : fact (a ≤ max b c) :=
⟨h.out.trans $ le_max_left _ _⟩

instance fact_one_le_mul_self (a : ℝ≥0) [h : fact (1 ≤ a)] : fact (1 ≤ a * a) :=
⟨calc (1 : ℝ≥0) = 1 * 1 : (mul_one 1).symm
           ... ≤ a * a : mul_le_mul' h.out h.out⟩

instance one_le_add {a b : ℝ≥0} [ha : fact (1 ≤ a)] : fact (1 ≤ a + b) :=
⟨le_trans ha.out $ by simp⟩
instance one_le_add' {a b : ℝ≥0} [hb : fact (1 ≤ b)] : fact (1 ≤ a + b) :=
⟨le_trans hb.out $ by simp⟩

instance fact_one_le_pow {n : ℕ} {a : ℝ≥0} [h : fact (1 ≤ a)] : fact (1 ≤ a^n) :=
begin
  cases n,
  { simpa only [pow_zero] using nnreal.fact_le_refl _ },
  { rwa one_le_pow_iff, apply nat.succ_ne_zero }
end

instance fact_pow_le_one {n : ℕ} {a : ℝ≥0} [h : fact (a ≤ 1)] : fact (a^n ≤ 1) :=
begin
  cases n,
  { simpa only [pow_zero] using nnreal.fact_le_refl _ },
  { rwa pow_le_one_iff, apply nat.succ_ne_zero }
end

lemma fact_le_pow_mul_of_le_pow_succ_mul {n : ℕ} (r : ℝ≥0)
  [fact (r ≤ 1)] [h : fact (c₂ ≤ r ^ (n+1) * c₁)] :
  fact (c₂ ≤ r ^ n * c₁) :=
begin
  refine ⟨h.out.trans _⟩,
  rw [pow_succ, mul_assoc],
  apply fact.out
end

instance fact_le_mul_add : fact (c * c₁ + c * c₂ ≤ c * (c₁ + c₂)) :=
by { rw mul_add, exact nnreal.fact_le_refl _ }

instance fact_nat_cast_pos (N : ℕ) [hN: fact (0 < N)] : fact (0 < (N:ℝ≥0)) :=
⟨nat.cast_pos.mpr hN.out⟩

end nnreal

#lint- only unused_arguments def_lemma doc_blame
