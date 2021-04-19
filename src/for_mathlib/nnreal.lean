import data.real.nnreal
import topology.instances.nnreal

open_locale nnreal

namespace nnreal

variables {R : Type*} [linear_ordered_comm_group_with_zero R]


lemma div_le_div_left_of_le {a b c : ℝ≥0} (b0 : 0 < b) (c0 : 0 < c) (cb : c ≤ b) :
  a / b ≤ a / c :=
begin
  by_cases a0 : a = 0,
  { rw [a0, zero_div, zero_div] },
  { cases a with a ha,
    replace a0 : 0 < a := lt_of_le_of_ne ha (ne_of_lt (zero_lt_iff.mpr a0)),
    exact (div_le_div_left a0 b0 c0).mpr cb }
end

lemma div_le_div_left {a b c : ℝ≥0} (a0 : 0 < a) (b0 : 0 < b) (c0 : 0 < c) :
  a / b ≤ a / c ↔ c ≤ b :=
by rw [nnreal.div_le_iff b0.ne.symm, div_mul_eq_mul_div, nnreal.le_div_iff_mul_le c0.ne.symm,
  mul_le_mul_left a0]

lemma pow_mono_decr_exp {a : ℝ≥0} (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) :
  a ^ n ≤ a ^ m :=
begin
  rcases le_iff_exists_add.mp mn with ⟨k, rfl⟩,
  rw [← mul_one (a ^ m), pow_add],
  refine mul_le_mul rfl.le (pow_le_one _ (zero_le a) a1) _ _;
  exact pow_nonneg (zero_le _) _,
end

end nnreal
