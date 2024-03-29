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

/-- If `0 < (p : ℝ≥0) < 1` and `S : Fintype` then `Θ p S` evaluates Laurent measures at 2⁻¹. -/
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

lemma psi_bound (S : Fintype) (c' : ℝ≥0) ⦃F : laurent_measures r S⦄ (hF1 : (Θ p S) F = 0)
  (hF2 : ∥F∥₊ ≤ c') : ∥ψ F hF1∥₊ ≤ c' * (2 - r⁻¹)⁻¹ :=
begin
  delta ψ,
  rw nnnorm_def at hF2 ⊢,
  simp only [coe_mk],
  delta Θ at hF1,
  have foo : ∀ (s : S), ∑' (n : ℤ), ∥ite (F.d ≤ n) ((finset.range (n - F.d).nat_abs.succ).sum
    (λ (l : ℕ), (F s (n - 1 - l) : ℝ) * 2 ^ l)) 0∥₊ * r ^ n ≤
    (2 - r⁻¹)⁻¹ * ∑' n, ∥(F s n : ℝ)∥₊ * r ^ n :=
  λ s, by convert psi_aux_lemma.key_tsum_lemma (λ n, (F s n : ℝ)) r r_lt_one half_lt_r F.d
    (λ n hnd, lt_d_eq_zero' F s n hnd) (F.summable' s) (congr_fun hF1 s),
  convert le_trans (finset.sum_le_sum (λ (s : S) _, foo s)) _,
  { norm_cast },
  simp_rw real.nnnorm_int,
  rw [← finset.mul_sum, mul_comm],
  exact (nnreal.mul_le_mul_right hF2 _),
end

theorem short_exact (S : Profinite) :
  short_exact ((condensify_Tinv2 _).app S) ((condensify_map $ Θ_fintype_nat_trans p).app S) :=
begin
  refine condensify_nonstrict_exact _ _ (r⁻¹ + 2) (Tinv2_bound_by _)
    -- C₂ bound (note that `2⁻¹ < r < 1` implies the max is always the left term)
    (λ c, max (c * ( r⁻¹ + 2) * ( 2 - r⁻¹)⁻¹) c)
    -- C₄ bound (note that `2⁻¹ < r < 1` implies that the max is always the left term)
    (λ c, max ((1 - r)⁻¹ * c) c)
    -- if you want to remove `max` from C₂ then you do that here
    (λ c, le_max_right _ c)
    -- if you want to remove `max` from C₄ then you do that here
    (λ c, le_max_right _ c)
    (λ S, injective_ϕ')
    (λ S, by { ext1 F, apply θ_ϕ_complex }) _ _ _,

    -- now two goals left, basically corresponding to
    -- existence of a bounded splitting of ϕ (namely ψ)
    -- and existence of a bounded splitting of θ
    -- (namely binary expansion).

    -- Here's a proof of the ϕ goal using ψ.
    { clear S,
      -- change to unbundled language
      rintros S c' (F : laurent_measures r S) ⟨(hF1 : Θ p S F = 0),
        (hF2 : ∥F∥₊ ≤ c')⟩,
      simp only [set.mem_image],
      refine ⟨ψ F hF1, _, θ_ϕ_split_exact F hF1⟩,
      change (∥_∥₊ : ℝ≥0) ≤ _,
      -- because of silly definition of `C₂` involving max :-)
      refine le_trans _ (mul_le_mul_right' (le_max_left _ _) _),
      convert psi_bound p S c' hF1 hF2 using 1,
      have h1 : 2⁻¹ < r := half_lt_r,
      have h2 : (2 - 1 / r) ≠ 0 := ne_of_gt (tsub_pos_of_lt
        (by { rw [one_div], exact r_inv_lt_2 })),
      have h3 : r ≠ 0 := ne_of_gt r_pos,
      field_simp,
      simp [mul_tsub, tsub_mul, one_div, mul_assoc, mul_inv_cancel h3],
      ring_nf, },
  -- Now here's a proof of the θ goal using binary expansions
    { clear S,
      rintros S c' (f : real_measures p S) (hf : _ ≤ _),
      let measure_aux : laurent_measures r S :=
      { to_fun := λ s n,
        if 0 ≤ f s then nnreal.int.binary (∥f s∥₊) n
        else -nnreal.int.binary (∥f s∥₊) n,
        summable' := λ s, begin
          convert nnreal.int.binary_summable (∥f s∥₊) (r_lt_one : r < 1),
          ext,
          split_ifs;
          simp,
        end },
      refine ⟨measure_aux, _⟩,
      change _ ≤ _ ∧ _,
      split,
      { refine le_trans _ (le_max_left _ _),
        refine le_trans _ (mul_le_mul_of_nonneg_left hf zero_le'),
        change finset.sum _ _ ≤ _ * finset.sum _ _,
        rw finset.mul_sum,
        refine finset.sum_le_sum (λ s _, _),
        rcases (eq_zero_or_pos : ∥f s∥₊ = 0 ∨ _) with (h0 | hpos),
        { simp [h0, measure_aux] },
        { convert le_trans (theta_aux_lemma.tsum_le
            (∥f s∥₊) (r_pos : 0 < r) (r_lt_one : r < 1)) _,
          { ext n, congr', dsimp [measure_aux], split_ifs; simp },
          { rw mul_comm,
            apply nnreal.mul_le_mul_left,
            rw ← nnreal.rpow_int_cast,
            convert nnreal.rpow_le_rpow_of_exponent_ge
              (r_pos : 0 < r) (r_lt_one.le) (int.le_ceil _) using 1,
            delta «r»,
            rw [← nnreal.rpow_mul, mul_comm, nnreal.rpow_mul],
            congr', symmetry,
            rw ← nnreal.coe_eq,
            exact nnreal.pow_log_div_log_self hpos (by norm_num) (by norm_num), } } },
      { delta Θ_fintype_nat_trans Θ θ_to_add θ theta.ϑ,
        dsimp,
        ext s,
        split_ifs,
        { convert nnreal.coe_eq.2 (nnreal.int.binary_sum ∥f s∥₊),
          push_cast, rw real.nnnorm_of_nonneg h, refl, },
        { convert neg_inj.2 (nnreal.coe_eq.2 (nnreal.int.binary_sum ∥f s∥₊)),
          { push_cast, rw ← tsum_neg, congr', ext, simp },
          { push_neg at h,
            rw real.neg_nnnorm_of_neg h, } } } },
end

end ses

end laurent_measures
