import data.real.nnreal
import topology.algebra.infinite_sum

open_locale big_operators

lemma tsum_abs_eq_coe_tsum_nnabs {α : Type*} (f : α → ℝ) :
  (∑' i, abs (f i)) = ∑' i, real.nnabs (f i) :=
by simp only [nnreal.coe_nnabs]
