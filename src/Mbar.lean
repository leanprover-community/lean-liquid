import ring_theory.power_series
import data.real.basic
import algebra.big_operators.basic
import topology.algebra.infinite_sum
import data.finset.basic
import data.equiv.basic
import .Mbar_bdd
/-

Scholze Analytic.pdf

p57, S finite

Mbar_r'(S)_{<=c}={(sum_{n≥1}a_{n,s}T^n)[s] | sum_{s,n}|a_{n,s}|r^n<=c}

-/

universe u

noncomputable theory
open_locale big_operators

open power_series

/-- `Mbar r' S c` is the set of power series
`F_s = ∑ a_{n,s}T^n ∈ ℤ[[T]]` such that `∑_{n,s} |a_{n,s}|r'^n ≤ c` -/
def Mbar (r' : ℝ) (S : Type u) [fintype S] (c : ℝ) :=
{F : S → power_series ℤ | (∀ s, constant_coeff ℤ (F s) = 0) ∧
  (∀ s, summable (λ n, abs ((power_series.coeff ℤ n (F s) : ℝ) * r'^n))) ∧
  (∑ s, ∑' n, (abs ((power_series.coeff ℤ n (F s) : ℝ) * r'^n))) ≤ c }

variables {r' : ℝ} {S : Type u} [fintype S] {c c₁ c₂ : ℝ}

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

def power_series.truncate (F : power_series ℤ) (M : ℕ) : fin (M+1) → ℤ :=
λ i, power_series.coeff _ i.1 F

lemma sum_fin_eq {M : ℕ} (f : ℕ → ℝ) : ∑ i in finset.range M, f i = ∑ (i : fin M), f i.1 :=
@finset.sum_bij' ℕ ℝ (fin M) _ (finset.range M) finset.univ f (λ i, f i.1)
  (λ a ha, ⟨a, finset.mem_range.mp ha⟩) (λ a ha, finset.mem_univ _) (λ a ha, rfl)
  (λ a _, a.1) (λ a ha, finset.mem_range.mpr a.2) (λ a ha, rfl) (λ a ha, by simp)

def truncate {hr : 0 < r'} {M : ℕ} : Mbar r' S c → Mbar_bdd r' hr ⟨S⟩ c M := λ F,
⟨λ s, (F.1 s).truncate M, begin
  rcases F with ⟨F,hF1,hF2,hF3⟩,
  refine ⟨λ s, by simpa [power_series.truncate] using hF1 s, le_trans _ hF3⟩,
  apply finset.sum_le_sum,
  intros s hs,
  have claim := @sum_le_tsum ℝ ℕ _ _ _ (λ n, abs ((power_series.coeff ℤ n (F s) : ℝ) * r'^n))
    (finset.range (M+1)) (λ b hb, abs_nonneg _) (hF2 s),
  erw sum_fin_eq (λ n, abs ((coeff ℤ n (F s) : ℝ) * r'^n)) at claim,
  convert claim,
  funext,
  dsimp only,
  rw [abs_mul, abs_of_pos (pow_pos hr _)],
  refl,
end⟩
