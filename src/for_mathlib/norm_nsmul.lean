import analysis.normed_space.basic

variables {A : Type*} [semi_normed_group A]

lemma norm_nsmul_le (n : ℕ) (a : A) : ∥n • a∥ ≤ n * ∥a∥ :=
begin
  induction n with n ih,
  { simp only [norm_zero, nat.cast_zero, zero_mul, zero_smul] },
  simp only [nat.succ_eq_add_one, add_smul, add_mul, one_mul, nat.cast_add,
    nat.cast_one, one_nsmul],
  exact norm_add_le_of_le ih le_rfl
end

lemma nnnorm_nsmul_le (n : ℕ) (a : A) : nnnorm (n • a) ≤ n * nnnorm a :=
by simpa only [←nnreal.coe_le_coe, nnreal.coe_mul, nnreal.coe_nat_cast]
  using norm_nsmul_le n a

lemma norm_gsmul_le (n : ℤ) (a : A) : ∥n • a∥ ≤ ∥n∥ * ∥a∥ :=
begin
  induction n with n n,
  { simp only [int.of_nat_eq_coe, gsmul_coe_nat],
    convert norm_nsmul_le n a,
    exact nat.abs_cast n },
  { simp only [int.neg_succ_of_nat_coe, neg_smul, norm_neg, gsmul_coe_nat],
    convert norm_nsmul_le n.succ a,
    exact nat.abs_cast n.succ, }
end

lemma nnnorm_gsmul_le (n : ℤ) (a : A) : nnnorm (n • a) ≤ nnnorm n * nnnorm a :=
by simpa only [←nnreal.coe_le_coe, nnreal.coe_mul] using norm_gsmul_le n a
