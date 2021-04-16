import data.real.nnreal

open_locale nnreal

variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]

namespace nnreal

lemma div_le_div_left_of_le {a b c : ℝ≥0} (b0 : 0 < b) (c0 : 0 < c) :
  c ≤ b → a / b ≤ a / c :=
begin
  by_cases a0 : a = 0,
  { exact λ _, by rw [a0, zero_div, zero_div] },
  { have ai : 0 < a := zero_lt_iff.mpr a0,
    cases a with a ha,
    cases b with b hb,
    cases c with c hc,
    have a00 : 0 < a := lt_of_le_of_ne ha (ne_of_lt ai),
    intros cb,
    erw [div_le_div_left a00 b0 c0],
    exact cb }
end

lemma pow_mono_decr_exp {a : ℝ≥0} (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) :
  a ^ n ≤ a ^ m :=
begin
  rcases le_iff_exists_add.mp mn with ⟨k, rfl⟩,
  rw [← mul_one (a ^ m), pow_add],
  refine mul_le_mul rfl.le (pow_le_one _ (zero_le a) a1) _ _;
  exact pow_nonneg (zero_le _) _,
end

end nnreal
