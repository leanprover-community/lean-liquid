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

lemma nnreal.eq_zero_or_pos (r : ℝ≥0) : r = 0 ∨ 0 < r :=
eq_zero_or_pos


variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
local notation `r` := @r p


example (S : Fintype) (s : ↥S)
  ⦃f : real_measures p S⦄
  (hpos : 0 < ∥f s∥₊)
  :
  let measure_aux : laurent_measures r S :=
        {to_fun := λ (s : ↥S) (n : ℤ),
                     ite (0 ≤ f s) ↑(theta_aux_lemma.binary ∥f s∥₊ n)
                       (-↑(theta_aux_lemma.binary ∥f s∥₊ n)),
         summable' := sorry}
  in r ^ ⌈real.log ↑∥f s∥₊ / real.log ↑(2⁻¹ : ℝ≥0)⌉ *
         (1 - r)⁻¹ ≤
       (1 - r)⁻¹ * ∥f s∥₊ ^ (p : ℝ) :=
begin
  intros measure_aux,
  -- cut and paste this
  rw mul_comm,
  apply nnreal.mul_le_mul_left,
  rw ← nnreal.rpow_int_cast,
  convert nnreal.rpow_le_rpow_of_exponent_ge (r_pos : 0 < r) (r_lt_one.le) (int.le_ceil _) using 1,
  delta «r»,
  rw [← nnreal.rpow_mul, mul_comm, nnreal.rpow_mul],
  congr', symmetry,
  rw ← nnreal.coe_eq,
  exact nnreal.pow_log_div_log_self hpos (by norm_num) (by norm_num),
end

open CompHausFiltPseuNormGrp₁

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
    sorry;{ clear S,
      -- change to unbundled language
      rintros S c' (F : laurent_measures r S) ⟨(hF1 : Θ p S F = 0),
        (hF2 : ∥F∥₊ ≤ c')⟩,
      simp only [set.mem_image],
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
          convert psi_aux_lemma.key_tsum_lemma (λ n, (F s n : ℝ)) r r_lt_one half_lt_r F.d
          (λ n hnd, lt_d_eq_zero' F s n hnd) (F.summable' s) (congr_fun hF1 s),
        end,
        convert le_trans (finset.sum_le_sum (λ (s : S) _, foo s)) _,
        { norm_cast },
        simp_rw real.nnnorm_int,
        rw ← finset.mul_sum,
        refine le_trans (nnreal.mul_le_mul_left hF2 _) _,
        apply le_of_eq,
        have h1 : 2⁻¹ < r := half_lt_r,
        have h2 : (2 - 1 / r) ≠ 0 := ne_of_gt (tsub_pos_of_lt
         (by { rw [one_div], exact r_inv_lt_2 })),
        have h3 : r ≠ 0 := ne_of_gt r_pos,
        field_simp,
        simp [mul_tsub, tsub_mul, one_div, mul_assoc, mul_inv_cancel h3],
        ring_nf, },
    exact θ_ϕ_split_exact F hF1 },
  -- Now here's a proof of the θ goal using binary expansions
  {
    clear S,
    rintros S c' (f : real_measures p S) (hf : _ ≤ _),
    let measure_aux : laurent_measures r S :=
    { to_fun := λ s n,
      if 0 ≤ f s then theta_aux_lemma.binary (∥f s∥₊) n
      else -theta_aux_lemma.binary (∥f s∥₊) n,
      summable' := λ s, begin
        convert theta_aux_lemma.summable_of_random_facts (∥f s∥₊) (r_lt_one : r < 1),
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
      { convert le_trans (theta_aux_lemma.tsum_le_of_random_facts (∥f s∥₊) (r_lt_one : r < 1)) _,
        { ext n, congr', dsimp [measure_aux], split_ifs; simp },
        { rw mul_comm,
          apply nnreal.mul_le_mul_left,
          rw ← nnreal.rpow_int_cast,
          convert nnreal.rpow_le_rpow_of_exponent_ge (r_pos : 0 < r) (r_lt_one.le) (int.le_ceil _) using 1,
          delta «r»,
          rw [← nnreal.rpow_mul, mul_comm, nnreal.rpow_mul],
          congr', symmetry,
          rw ← nnreal.coe_eq,
          exact nnreal.pow_log_div_log_self hpos (by norm_num) (by norm_num), } } },
    { delta Θ_fintype_nat_trans,
      dsimp,
      delta Θ θ_to_add θ theta.ϑ,
      dsimp,
      sorry} },
end

end ses

end laurent_measures
