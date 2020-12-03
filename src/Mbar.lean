import ring_theory.power_series
import data.real.basic
import algebra.big_operators.basic
import topology.algebra.infinite_sum
/-

Scholze Analytic.pdf

p57, S finite

Mbar_r'(S)_{<=c}={(sum_{n≥1}a_{n,s}T^n)[s] | sum_{s,n}|a_{n,s}|r^n<=c}

-/

universe u

open_locale big_operators

open power_series

/-- `Mbar r' S c` is the set of power series
`F_s = ∑ a_{n,s}T^n ∈ ℤ[[T]]` such that `∑_{n,s} |a_{n,s}|r'^n ≤ c` -/
def Mbar (r' : ℝ) (S : Type u) [fintype S] (c : ℝ) :=
{F : S → power_series ℤ | (∀ s, constant_coeff ℤ (F s) = 0) ∧
  (∀ s, summable (λ n, abs ((power_series.coeff ℤ n (F s) : ℝ) * r'^n))) ∧
  (∑ s, ∑' n, (abs ((power_series.coeff ℤ n (F s) : ℝ) * r'^n))) ≤ c }

variables {r' : ℝ} {S : Type u} [fintype S] {c₁ c₂ : ℝ}

noncomputable def Mbar.add :
  Mbar r' S c₁ → Mbar r' S c₂ → Mbar r' S (c₁ + c₂) :=
λ F G, ⟨F + G, begin
  rcases F with ⟨F, hF0, hFs, hFsc⟩,
  rcases G with ⟨G, hG0, hGs, hGsc⟩,
  show F + G ∈ _,
  have hFGs : ∀ (s : S), summable (λ (n : ℕ), abs (↑((coeff ℤ n) ((F + G) s)) * r' ^ n)),
  { intro s,
    simp_rw summable_abs_iff at hFs hGs ⊢,
    convert summable.add (hFs s) (hGs s),
    ext n,
    simp [add_mul] },
  refine ⟨_, hFGs, _⟩,
  { intro s,
    simp [hF0 s, hG0 s] },
  { refine le_trans _ (add_le_add hFsc hGsc),
    rw ← finset.sum_add_distrib,
    apply finset.sum_le_sum,
    rintro s -,
    rw ← tsum_add (hFs s) (hGs s),
    refine tsum_le_tsum _ (hFGs s) _,
    { intro n,
      convert abs_add _ _,
      simp [add_mul] },
    { exact summable.add (hFs s) (hGs s) } }
end⟩
