import data.real.nnreal
import analysis.mean_inequalities_pow
import for_mathlib.ennreal

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

attribute [norm_cast] nnreal.coe_zpow

open_locale ennreal big_operators

/-- sum of row sums equals sum of column sums -/
lemma nnreal.summable_symm {α β: Type*} (F : α → β → ℝ≥0)
  (h_rows : ∀ n, summable (λ k, F n k)) (h_cols : ∀ k, summable (λ n, F n k))
  (h_col_row : summable (λ k, ∑' n, F n k)) : summable (λ n, ∑' k, F n k) :=
begin
  cases h_col_row with a ha,
  use a,
  rw ← ennreal.has_sum_coe,
  convert_to has_sum (λ n, ∑' k, (F n k : ℝ≥0∞)) a,
  { ext1 n,
    exact ennreal.coe_tsum (h_rows n) },
  { rw ennreal.has_sum_comm,
    rw ← ennreal.has_sum_coe at ha,
    convert ha,
    ext1 k,
    exact (ennreal.coe_tsum (h_cols k)).symm },
end

open nnreal

lemma nnreal.summable_of_comp_injective {α β : Type*} {f : α → ℝ≥0} {i : β → α}
  (hi : function.injective i) (hi' : ∀ a, a ∉ set.range i → f a = 0) (hfi : summable (f ∘ i)) :
  summable f :=
begin
  rw ← summable_coe at hfi ⊢,
  let e : β ≃ ({x : α | x ∈ set.range i} : set α) :=
  { to_fun := λ b, ⟨i b, b, rfl⟩,
  inv_fun := λ x, x.2.some,
  left_inv := begin intro b, simp, apply hi, exact Exists.some_spec (⟨b, rfl⟩ : ∃ y, i y = i b) end,
  right_inv := begin rintro ⟨x, b, rfl⟩, simp, exact Exists.some_spec (⟨b, rfl⟩ : ∃ y, i y = i b) end },
  have this2 : summable ((λ (x : {x : α // x ∈ set.range i}), (f x.1 : ℝ)) ∘ ⇑e : β → ℝ),
  { convert (summable_congr _).1 hfi,
    intro b, refl },
  rw e.summable_iff at this2,
  change summable ((λ a, (f a : ℝ)) ∘ (coe : {x // x ∈ set.range i} → α)) at this2,
  rw ← this2.summable_compl_iff,
  convert summable_zero,
  ext1 ⟨x, hx⟩,
  simp [hi' x hx],
end

lemma nnreal.summable_subtype {β : Type*} {f : β → ℝ≥0} (hf : summable f)
  (s : set β) :  summable (f ∘ (coe : s → β)) :=
begin
  rw ← summable_coe at ⊢ hf,
  exact hf.subtype s,
end

lemma nnreal.mul_le_mul_right {a b : ℝ≥0} (h : a ≤ b) (c : ℝ≥0) : a * c ≤ b * c :=
begin
  suffices : (a : ℝ) * c ≤ b * c, by assumption_mod_cast,
  apply mul_le_mul_of_nonneg_right (by assumption_mod_cast),
  apply zero_le',
end

lemma nnreal.mul_le_mul_left {a b : ℝ≥0} (h : a ≤ b) (c : ℝ≥0) : c * a ≤ c * b :=
by simpa [mul_comm] using nnreal.mul_le_mul_right h c

lemma nnreal.rpow_sum_le_sum_rpow
  {ι : Type*} (s : finset ι) {p : ℝ} (a : ι → ℝ≥0) (hp_pos : 0 < p) (hp1 : p ≤ 1) :
  (∑ i in s, a i) ^ p ≤ ∑ i in s, (a i ^ p) :=
begin
  classical,
  induction s using finset.induction_on with i s his IH,
  { simp only [nnreal.zero_rpow hp_pos.ne', finset.sum_empty, le_zero_iff], },
  { simp only [his, finset.sum_insert, not_false_iff],
    exact (nnreal.rpow_add_le_add_rpow _ _ hp_pos hp1).trans (add_le_add le_rfl IH), }
end

lemma nnreal.le_self_rpow {a : ℝ≥0} {m : ℝ} (ha : 1 ≤ a) (hm : 1 ≤ m) : a ≤ a ^ m :=
begin
  suffices : a ^ (1 : ℝ) ≤ a ^ m,
    simpa,
  exact rpow_le_rpow_of_exponent_le ha hm,
end


lemma nnreal.le_self_rpow' {a : ℝ≥0} {m : ℝ} (ha : a ≤ 1) (hm : m ≤ 1) : a ≤ a ^ m :=
begin
  obtain (rfl|⟨u, rfl⟩) := group_with_zero.eq_zero_or_unit a, apply zero_le, -- a=0 special case
  suffices : (u : ℝ≥0) ^ (1 : ℝ) ≤ u ^ m,
    simpa,
  exact rpow_le_rpow_of_exponent_ge (by simp) ha hm,
end

-- no need to prove for nnreal because need positive (not non-negative)
lemma real.injective_log {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (h : real.log r = real.log s) : r = s :=
begin
  apply_fun real.exp at h,
  rwa [real.exp_log hr, real.exp_log hs] at h,
end

lemma nnreal.pow_log_div_log_self {r : ℝ} {s : ℝ} (hr : 0 < r) (hs : 0 < s) (hs' : s ≠ 1) :
  s ^ (real.log r / real.log s) = r :=
begin
  apply real.injective_log (real.rpow_pos_of_pos hs _) hr,
  rw real.log_rpow hs,
  rw ← eq_div_iff,
  apply mt (λ h, _) hs',
  rw real.log_eq_zero at h,
  rcases h with (h|h|h); linarith,
end

lemma nnreal.div_inv {a b : ℝ≥0} : a / b⁻¹ = a * b :=
begin
  rcases eq_or_ne b 0 with (rfl | hb),
  { rw [inv_zero, div_zero, mul_zero] },
  rw [div_eq_iff (inv_ne_zero hb), mul_assoc, mul_inv_cancel hb, mul_one],
end

lemma nnreal.tsum_le_tsum {X : Type*} {f g : X → ℝ≥0} (hle : ∀ x, f x ≤ g x)
  (hsummable : summable g) : ∑' x, f x ≤ ∑' x, g x :=
tsum_le_tsum hle (summable_of_le hle hsummable) hsummable
