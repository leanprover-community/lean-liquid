import laurent_measures.ses
import laurent_measures.condensed
import real_measures.condensed
import condensed.condensify
import laurent_measures.prop72 -- kmb's attempt to tidy up the analysis argument

universe u

noncomputable theory

open category_theory

open_locale nnreal

namespace laurent_measures

open laurent_measures_ses ProFiltPseuNormGrpWithTinv₁

section theta

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
local notation `r` := @r p

/-- If `0 < (p : ℝ≥0) < 1` and `S : Fintype` then Θ p S-/
def Θ (S : Fintype.{u}) :
  (Fintype_LaurentMeasures.{u} r ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ.{u} r).obj S ⟶
  (real_measures.functor p).obj S :=
strict_comphaus_filtered_pseudo_normed_group_hom.mk' (θ_to_add p)
begin
  intro c,
  use θ_bound' p c,
  convert continuous_θ_c p S c,
  simp only [θ_c, one_mul, eq_mpr_eq_cast, set_coe_cast],
  refl,
end

def Θ_fintype_nat_trans :
  (Fintype_LaurentMeasures.{u} r ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ.{u} r) ⟶ (real_measures.functor.{u} p) :=
{ app := λ S, Θ p S,
  naturality' := λ S T f, by { ext x t, apply θ_natural, } }
.

end theta

section ses

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
local notation `r` := @r p

open CompHausFiltPseuNormGrp₁

theorem short_exact (S : Profinite) :
  short_exact ((condensify_Tinv2 _).app S) ((condensify_map $ Θ_fintype_nat_trans p).app S) :=
begin
  refine condensify_nonstrict_exact _ _ (r⁻¹ + 2) (Tinv2_bound_by _)
  -- C₂ bound
  (λ c, max (c * ( r⁻¹ + 2) * ( 2 - r⁻¹)⁻¹) c)
  -- C₄ bound
  (λ c, max (2 * (1 - r)⁻¹) c)
  (λ c, le_max_right _ c)
  -- fill this in f(x)>=x proof when I know what C₄ actually is (it's not 37).
  (λ c, le_max_right _ c)
  (λ S, injective_ϕ')
  (λ S, by { ext1 F, apply θ_ϕ_complex }) _ _ _,
  -- proof of some boundedness thing
  sorry;{ clear S,
    -- change to unbundled language
    rintros S c' (F : laurent_measures r S) ⟨(hF1 : Θ p S F = 0),
      (hF2 : ∥F∥₊ ≤ c')⟩,
    simp only [set.mem_image],
--    change ∃ x : laurent_measures r S,
 --     ∥x∥₊ ≤ (c' * ( 1 + 2 * r) / ( 2 * r - 1)) * («r»⁻¹ + 2)⁻¹ ∧ _,
--sorry, }, all_goals {sorry} end #exit
    refine ⟨ψ F hF1, _, _⟩,
    --let ZZZ := ϕ f r,
    { delta ψ,
      change (∥_∥₊ : ℝ≥0) ≤ _,
      rw nnnorm_def at hF2 ⊢,
      simp only [coe_mk],
      delta Θ at hF1,
      rw mul_assoc,
      -- because of silly definition of `C₂` involving max :-)
      refine le_trans _ (mul_le_mul_right' (le_max_left _ _) _),
      have foo : ∀ (s : S), ∑' (n : ℤ), ∥ite (F.d ≤ n) ((finset.range (n - F.d).nat_abs.succ).sum
        (λ (l : ℕ), (F s (n - 1 - l) : ℝ) * 2 ^ l)) 0∥₊ * r ^ n ≤
        (2 - r⁻¹)⁻¹ * ∑' n, ∥(F s n : ℝ)∥₊ * r ^ n :=
        λ s,
      begin
        convert psi_aux_lemmas.key_tsum_lemma (λ n, (F s n : ℝ)) r r_lt_one half_lt_r F.d
        (λ n hnd, lt_d_eq_zero' F s n hnd) (F.summable' s) (congr_fun hF1 s),
      end,
      convert le_trans (finset.sum_le_sum (λ (s : S) _, foo s)) _,
      { norm_cast },
      simp_rw real.nnnorm_int,
      rw ← finset.mul_sum,
      refine le_trans (nnreal.mul_le_mul_left hF2 _) _,
      apply le_of_eq,
      have h1 : 2⁻¹ < r := half_lt_r,
      have h2 : (2 - 1 / r) ≠ 0, sorry,
      have h3 : r ≠ 0, sorry,
      field_simp,
      simp [mul_tsub, tsub_mul, one_div, mul_assoc, mul_inv_cancel h3],
      ring_nf, },
    exact θ_ϕ_split_exact F hF1 },
  { -- C₄ proof: need to fix 37 thing first.
    clear S,
    rintros S c' (f : real_measures p S) (hf : _ ≤ _),
    refine ⟨_, _⟩,
    change laurent_measures r S, sorry,
    -- need to define some new data here
    change _ ≤ _ ∧ _,
    delta Θ_fintype_nat_trans,
    dsimp,
    delta Θ θ_to_add θ theta.ϑ,
    dsimp,
    sorry },
end

end ses

end laurent_measures
