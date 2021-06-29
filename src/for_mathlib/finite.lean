import data.fintype.intervals

noncomputable theory
open set

-- PR #8123

instance (a b : ℤ) : fintype (Icc a b) := nonempty.some (Icc_ℤ_finite a b)
instance (a b : ℤ) : fintype (Ioc a b) := nonempty.some (Ioc_ℤ_finite a b)
instance (a b : ℤ) : fintype (Ioo a b) := nonempty.some (Ioo_ℤ_finite a b)
