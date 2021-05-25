import data.real.nnreal

open_locale nnreal

lemma nnreal.le_div_iff {a b c : ℝ≥0} (h : c ≠ 0) : a ≤ b / c ↔ a * c ≤ b :=
@le_div_iff ℝ _ a b c $ pos_iff_ne_zero.2 h

lemma nnreal.le_div_iff' {a b c : ℝ≥0} (h : c ≠ 0) : a ≤ b / c ↔ c * a ≤ b :=
@le_div_iff' ℝ _ a b c $ pos_iff_ne_zero.2 h

lemma nnreal.div_le_iff' {a b c : ℝ≥0} (h : b ≠ 0) : a / b ≤ c ↔ a ≤ b * c :=
@div_le_iff' ℝ _ a b c $ pos_iff_ne_zero.2 h

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
