import data.rat.nnrat

/-!
# Nonnegative rationals

## TODO

* Rename `nnrat.to_nnrat_mono` to `rat.to_nnrat_mono`.
* Coercion to `nnreal`.
-/

open_locale big_operators nnrat

namespace nnrat

attribute [derive canonically_linear_ordered_add_monoid] nnrat

lemma bot_eq_zero : (⊥ : ℚ≥0) = 0 := rfl

lemma mul_sup (a b c : ℚ≥0) : a * (b ⊔ c) = (a * b) ⊔ (a * c) :=
begin
  cases le_total b c with h h,
  { simp [sup_eq_max, max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h (zero_le a))] },
  { simp [sup_eq_max, max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h (zero_le a))] }
end

lemma mul_finset_sup {α} {f : α → ℚ≥0} {s : finset α} (r : ℚ≥0) :
  r * s.sup f = s.sup (λa, r * f a) :=
begin
  classical,
  refine s.induction_on _ _,
  { simp [bot_eq_zero] },
  { assume a s has ih, simp [has, ih, mul_sup] }
end

section inv

lemma sum_div {ι} (s : finset ι) (f : ι → ℚ≥0) (b : ℚ≥0) :
  (∑ i in s, f i) / b = ∑ i in s, (f i / b) :=
by simp only [div_eq_mul_inv, finset.sum_mul]

@[simp] lemma inv_le {r p : ℚ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p :=
by rw [←mul_le_mul_left h.bot_lt, mul_inv_cancel h]

lemma inv_le_of_le_mul {r p : ℚ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p :=
by by_cases r = 0; simp [*, inv_le]

@[simp] lemma le_inv_iff_mul_le {r p : ℚ≥0} (h : p ≠ 0) : (r ≤ p⁻¹ ↔ r * p ≤ 1) :=
by rw [←mul_le_mul_left h.bot_lt, mul_inv_cancel h, mul_comm]

@[simp] lemma lt_inv_iff_mul_lt {r p : ℚ≥0} (h : p ≠ 0) : (r < p⁻¹ ↔ r * p < 1) :=
by rw [←mul_lt_mul_left h.bot_lt, mul_inv_cancel h, mul_comm]

lemma mul_le_iff_le_inv {a b r : ℚ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
have 0 < r, from lt_of_le_of_ne (zero_le r) hr.symm,
by rw [←mul_le_mul_left (inv_pos.2 this), ←mul_assoc, inv_mul_cancel hr, one_mul]

lemma lt_div_iff {a b r : ℚ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
lt_iff_lt_of_le_iff_le (div_le_iff₀ hr)

lemma mul_lt_of_lt_div {a b r : ℚ≥0} (h : a < b / r) : a * r < b :=
(lt_div_iff $ by { rintro rfl, simpa using h }).1 h

lemma le_of_forall_lt_one_mul_le {x y : ℚ≥0} (h : ∀a<1, a * x ≤ y) : x ≤ y :=
le_of_forall_ge_of_dense $ assume a ha,
  have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha),
  have hx' : x⁻¹ ≠ 0, by rwa [(≠), inv_eq_zero],
  have a * x⁻¹ < 1, by rwa [←lt_inv_iff_mul_lt hx', inv_inv],
  have (a * x⁻¹) * x ≤ y, from h _ this,
  by rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this

lemma half_lt_self {a : ℚ≥0} (h : a ≠ 0) : a / 2 < a := half_lt_self h.bot_lt

lemma two_inv_lt_one : (2⁻¹:ℚ≥0) < 1 := by simpa using half_lt_self zero_ne_one.symm

lemma div_lt_iff {a b c : ℚ≥0} (hc : c ≠ 0) : b / c < a ↔ b < a * c :=
lt_iff_lt_of_le_iff_le $ le_div_iff₀ hc

lemma div_lt_one_of_lt {a b : ℚ≥0} (h : a < b) : a / b < 1 :=
begin
  rwa [div_lt_iff, one_mul],
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)
end

end inv

@[simp] lemma abs_eq (x : ℚ≥0) : abs (x : ℚ) = x := abs_of_nonneg x.property

end nnrat
