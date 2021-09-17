import data.real.nnreal

open_locale nnreal

-- There doesn't seem to be a real analogue of this one, but probably should be?
lemma nnreal.div_le_div_left_of {a b c : ℝ≥0} (w : 0 < c) (h : c ≤ b) : a / b ≤ a / c :=
begin
  rcases a with ⟨a, a_pos⟩,
  rcases b with ⟨b, b_pos⟩,
  rcases c with ⟨c, c_pos⟩,
  change a / b ≤ a / c,
  change 0 < c at w,
  change c ≤ b at h,
  by_cases p : 0 < a,
  { rw div_le_div_left p (lt_of_lt_of_le w h) w,
    exact h, },
  { have q : a = 0, linarith,
    subst q,
    simp, }
end

@[simp, norm_cast] lemma nnreal.coe_fpow (x : ℝ≥0) (n : ℤ) : ((x ^ n : ℝ≥0) : ℝ) = x ^ n :=
begin
  induction n with n ih;
  simp only [int.of_nat_eq_coe, nnreal.coe_pow, gpow_coe_nat, gpow_neg_succ_of_nat, nnreal.coe_inv]
end
