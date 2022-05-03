import for_mathlib.nnreal_nat_binary

open_locale nnreal

-- Scholze's definition
noncomputable def intbinary (r : ℝ≥0) : ℤ → ℕ :=
if r = 0 then 0 else
λ n, let d : ℤ := ⌈(r : ℝ).log / (2⁻¹ : ℝ).log⌉ in
if n < d then 0 else nnreal.digit (r * 2⁻¹ ^ (n - d)) (n - d).nat_abs

/-
r > 0; now need biggest d : ℤ such that 2⁻¹ ^ d ≤ r
2^(-d)<=r
(-d) log 2 <= log r
(-d) <= log r / log 2
d >= -log(r)/log(2)=log(r)/(-log(2))=log(r)/log(2⁻¹)
-/

--theorem binary_le_one (r : ℝ≥0) (z : ℤ) : binary r z ≤ 1 := sorry

--theorem binary_sum (r : ℝ≥0) : ∑' (n : ℤ), (binary r n : ℝ≥0) * 2⁻¹ ^ n = r := sorry
