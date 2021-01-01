import analysis.normed_space.basic

section

variables {V : Type*} [normed_group V]

lemma norm_nsmul_le (n : ℕ) (v : V) : ∥n •ℕ v∥ ≤ n * ∥v∥ :=
begin
  induction n with n ih,
  { simp only [norm_zero, nat.cast_zero, zero_mul, zero_nsmul] },
  { simp only [nat.succ_eq_add_one, add_nsmul, nat.cast_add,
      nat.cast_one, one_nsmul, add_mul, one_mul],
    calc ∥n •ℕ v + v∥
        ≤ ∥n •ℕ v∥ + ∥v∥ : norm_add_le _ _
    ... ≤ n * ∥v∥ + ∥v∥ : add_le_add_right ih _ }
end

lemma norm_gsmul_le (n : ℤ) (v : V) : ∥n •ℤ v∥ ≤ (abs n) * ∥v∥ :=
begin
  induction n,
  { simpa only [int.cast_coe_nat, int.of_nat_eq_coe, gsmul_coe_nat, nat.abs_cast]
      using norm_nsmul_le n v },
  { simpa only [gsmul_neg_succ_of_nat, abs_neg, norm_neg, int.cast_neg_succ_of_nat,
    ← nat.cast_add_one, nat.abs_cast] using norm_nsmul_le (n+1) v }
end

end
