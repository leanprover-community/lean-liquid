import analysis.normed_space.basic

open_locale nnreal

-- move this
@[simp] lemma nnreal.coe_nat_abs (n : ℤ) : ↑n.nat_abs = nnnorm n :=
nnreal.eq $
calc ((n.nat_abs : ℝ≥0) : ℝ)
    = ↑(n.nat_abs : ℤ) : by simp only [int.cast_coe_nat, nnreal.coe_nat_cast]
... = abs n            : by simp only [← int.abs_eq_nat_abs, int.cast_abs]
... = ∥n∥               : rfl
