import data.real.nnreal

open_locale nnreal

-- PR 8121
lemma cast_nat_abs_eq_nnabs_cast (n : ℤ) :
  (n.nat_abs : ℝ≥0) = real.nnabs n :=
by { ext, rw [nnreal.coe_nat_cast, int.cast_nat_abs, nnreal.coe_nnabs] }
