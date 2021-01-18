import data.real.nnreal

open_locale nnreal

instance nnreal.le_mul_of_one_le_left (k c : ℝ≥0) [hk : fact (1 ≤ k)] :
  fact (c ≤ k * c) :=
le_mul_of_one_le_left c.2 hk
