import free_pfpng.main
import invpoly.functor
import condensed.condensify
import laurent_measures.thm69
import normed_free_pfpng.compare
import Lbar.ses
import laurent_measures.ses2

universe u

noncomputable theory

open category_theory

open_locale nnreal big_operators

namespace invpoly
open ProFiltPseuNormGrpWithTinv₁

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]

local notation `r` := @r p

/-- The "evaluate at 2" function, sending an S-indexed family of elements of `ℤ[T⁻¹]`
  to an S-indexed family of integers, via the assignment `T⁻¹ ↦ 2`. Note that
  this is a strict (i.e. norm-nonincreasing) morphism of normed groups,
  with the norm on a polynomial `∑aₙT⁻ⁿ` being `∑ₙ∥aₙ∥₊r⁻ⁿ` and the norm
  on an integer `z` being `∥z∥₊ᵖ`; this works because `r = 2⁻ᵖ`, the crucial
  points being that `(∑∥cₙ∥)ᵖ ≤ ∑(∥cₙ∥ᵖ)` as `0 < p ≤ 1`, and `∥z∥ᵖ ≤ ∥z∥` for an integer `z`.   -/
@[simps] def eval2 (S : Fintype.{u}) :
  strict_comphaus_filtered_pseudo_normed_group_hom (invpoly r S) (normed_free_pfpng p S) :=
{ to_fun := λ F s, (F s).eval 2,
  map_zero' := by { ext, simp only [polynomial.eval_zero, pi.zero_apply], },
  map_add' := by { intros, ext, simp only [polynomial.eval_add, pi.add_apply], },
  strict' := λ c F hF, begin
    refine (finset.sum_le_sum _).trans hF,
    rintro s -,
    have h0p : 0 < p := fact.out _,
    have hp1 : p ≤ 1 := fact.out _,
    have h0pinv : 0 ≤ p⁻¹, { rw ← nnreal.inv_pos at h0p, exact h0p.le },
    calc ∥(F s).eval 2∥₊ ^ (p:ℝ)
        = ∥∑ n in finset.range ((F s).nat_degree + 1), (F s).coeff n * 2 ^ n∥₊ ^ (p:ℝ) : _
    ... ≤ (∑ n in finset.range ((F s).nat_degree + 1), ∥(F s).coeff n * 2 ^ n∥₊) ^ (p:ℝ) : _
    ... ≤ ∑ n in finset.range ((F s).nat_degree + 1), (∥(F s).coeff n * 2 ^ n∥₊ ^ (p:ℝ)) : _
    ... ≤ ∑ n in finset.range ((F s).nat_degree + 1), (∥(F s).coeff n∥₊ * r ^ (-n:ℤ)) : _
    ... ≤ ∑' n, (∥(F s).coeff n∥₊ * r ^ (-n:ℤ)) : _,
    { rw polynomial.eval_eq_sum_range, },
    { refine nnreal.rpow_le_rpow (nnnorm_sum_le _ _) h0p.le, },
    { refine nnreal.rpow_sum_le_sum_rpow _ _ h0p hp1, },
    { refine finset.sum_le_sum _,
      intros n hn,
      rw [int.nnnorm_mul, nnreal.mul_rpow],
      refine mul_le_mul' _ (le_of_eq _),
      { exact nnnorm_int_rpow_le p _ },
      { have h2n : (2 ^ n : ℤ) = (2 ^ n : ℕ), { norm_cast, },
        simp only [h2n, ← nnreal.coe_nat_abs, int.nat_abs_of_nat],
        rw [zpow_neg₀, ← inv_zpow₀, zpow_coe_nat],
        calc ((2 ^ n : ℕ) : ℝ≥0) ^ (p:ℝ)
            = (2 ^ (n:ℝ) : ℝ≥0) ^ (p:ℝ) : _
        ... = (2⁻¹ ^ (p:ℝ) : ℝ≥0)⁻¹ ^ (n:ℝ) : _
        ... = r⁻¹ ^ n : _,
        { norm_cast },
        { rw [← nnreal.rpow_mul, mul_comm, nnreal.rpow_mul, ← nnreal.inv_rpow, inv_inv], },
        { rw [nnreal.rpow_nat_cast], refl, } } },
    { refine sum_le_tsum _ _ _,
      { intros, exact zero_le' },
      { exact F.nnreal_summable s } },
  end,
  continuous' := λ c, continuous_of_discrete_topology }

/-- The "evaluate a polynomial in `T⁻¹` by mapping `T⁻¹` to `2`" functor
 from `ℤ[T⁻¹]` to `ℤ`. -/
def eval2_nat_trans :
  (Fintype_invpoly.{u} r ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ.{u} r) ⟶
  (normed_free_pfpng_functor.{u} p ⋙ PFPNG₁_to_CHFPNG₁ₑₗ) :=
{ app := λ S, eval2 p S,
  naturality' := λ S T f, begin
    ext x t,
    show (map f x t).eval 2 = _,
    dsimp only [functor.comp_map, normed_free_pfpng_functor_map,
      CompHausFiltPseuNormGrp₁.comp_apply, map],
    erw [polynomial.eval_finset_sum], refl, recover, exact 0,
  end }
.

section ses

open CompHausFiltPseuNormGrp₁

-- move this
instance (M N : Type*)
  [comphaus_filtered_pseudo_normed_group M] [comphaus_filtered_pseudo_normed_group N] :
  add_monoid_hom_class (comphaus_filtered_pseudo_normed_group_hom M N) M N :=
{ coe := λ f, f,
  coe_injective' := λ f g h, by { ext, dsimp at h, rw h },
  map_add := λ f, f.map_add,
  map_zero := λ f, f.map_zero }

lemma Tinv2_injective (S : Fintype) :
  function.injective ((Tinv2_nat_trans (Fintype_invpoly r)).app S) :=
begin
  rw injective_iff_map_eq_zero,
  intros f hf,
  ext s n,
  apply_fun (λ φ, φ s) at hf,
  simp only [Tinv2_nat_trans, Tinv_nat_trans, nat_trans.app_nsmul, nat_trans.id_app, sub_apply,
    nat_trans.app_sub, comphaus_filtered_pseudo_normed_group_hom.sub_apply,
    pi.nsmul_apply, comphaus_filtered_pseudo_normed_group_hom.nsmul_apply,
    pi.sub_apply, pi.zero_apply] at hf,
  simp only [pi.zero_apply, polynomial.coeff_zero],
  induction n with n ih,
  { apply_fun (λ φ, φ.coeff 0) at hf,
    simp only [polynomial.coeff_zero, polynomial.coeff_sub, polynomial.coeff_smul] at hf,
    erw [invpoly.Tinv_zero, zero_sub, neg_eq_zero, two_nsmul_eq_zero ℤ ℤ] at hf, exact hf, },
  { apply_fun (λ φ, φ.coeff (n+1)) at hf,
    simp only [polynomial.coeff_zero, polynomial.coeff_sub, polynomial.coeff_smul] at hf,
    erw [invpoly.Tinv_succ, ih, zero_sub, neg_eq_zero, two_nsmul_eq_zero ℤ ℤ] at hf, exact hf }
end

lemma Tinv2_comp_eval2_eq_zero (S : Fintype) :
  (Tinv2_nat_trans (Fintype_invpoly r)).app S ≫
    (whisker_right (eval2_nat_trans p) CHFPNG₁_to_CHFPNGₑₗ).app S = 0 :=
begin
  ext f s,
  show (polynomial.X * (f s) - _).eval 2 = (0 : ℤ),
  simp only [nat_trans.app_nsmul, nat_trans.id_app, comphaus_filtered_pseudo_normed_group_hom.nsmul_apply,
  category_theory.id_apply, pi.smul_apply, nsmul_eq_mul, nat.cast_bit0, nat.cast_one, polynomial.eval_sub,
  polynomial.eval_mul, polynomial.eval_X, polynomial.eval_bit0, polynomial.eval_one, sub_self],
end
.

lemma theta_eval2_aux {S : Fintype} (s : S) (c : ℝ≥0) {f : invpoly r S} :
  ∑' (n : ℤ), (to_laurent_measures_fun r S f s n : ℝ) * ((2 : ℝ) ^ n)⁻¹ = ↑(polynomial.eval 2 (f s)) :=
begin
  rw polynomial.eval_eq_sum_range,
  have this : ∀ (n : ℤ),
  n ∉ finset.Icc (-(f s).nat_degree : ℤ) 0 →
  (λ (b : ℤ), ↑(to_laurent_measures_fun «r» S f s b) * ((2 : ℝ) ^ b)⁻¹) n = 0,
  { rintros n hn,
    rw [finset.mem_Icc, not_and_distrib] at hn,
    push_neg at hn,
    dsimp only,
    convert zero_mul _,
    norm_cast,
    cases hn with hn hn,
    { have : ∃ m : ℕ, n = - m,
      { use n.nat_abs,
        rw int.nat_abs_of_nonpos,
        { simp },
        exact le_trans hn.le (by simp), },
      rcases this with ⟨m, rfl⟩,
      rw to_laurent_measures_fun_nonpos,
      rw polynomial.coeff_eq_zero_of_nat_degree_lt,
      simpa using hn },
    { have : ∃ m : ℕ, n = m + 1,
      { use (n - 1).nat_abs,
        rw int.nat_abs_of_nonneg,
        ring, linarith, },
      rcases this with ⟨m, rfl⟩,
      apply to_laurent_measures_fun_pos' } },
  rw tsum_eq_sum this, clear this,
  push_cast,
  apply finset.sum_bij (λ (n : ℤ) hn, n.nat_abs),
  -- this is supposed to be the easy one! all that remains
  -- is four boring pieces of easy nonsense e.g.
  --2^{-n}=2^{n.nat_abs} if n < 0 is probably the hardest one
  { intros a ha,
    suffices : a.nat_abs < (f s).nat_degree + 1,
    { simpa },
    rw finset.mem_Icc at ha,
    rw [nat.lt_succ_iff, ← int.coe_nat_le, int.nat_abs_of_nonpos ha.2],
    linarith [ha.1] },
  { intros a ha,
    rw finset.mem_Icc at ha,
    simp only,
    congr,
    { have : ∃ m : ℕ, a = - m,
      { use a.nat_abs,
        rw int.nat_abs_of_nonpos ha.2,
        simp, },
      rcases this with ⟨m, rfl⟩,
      rw to_laurent_measures_fun_nonpos,
      congr,
      rw [← int.coe_nat_eq_coe_nat_iff, int.nat_abs_of_nonpos ha.2, neg_neg], },
    { rw [← zpow_neg₀, ← int.nat_abs_of_nonpos ha.2, zpow_coe_nat], } },
  { rintros a b ha hb (habs : a.nat_abs = b.nat_abs),
    rw finset.mem_Icc at ha hb,
    rw [← int.coe_nat_eq_coe_nat_iff, int.nat_abs_of_nonpos ha.2,
      int.nat_abs_of_nonpos hb.2] at habs,
    exact neg_inj.mp habs },
  { intros a ha,
    rw [finset.mem_range_succ_iff] at ha,
    refine ⟨-(a : ℤ), _, _⟩,
    { rw [finset.mem_Icc, neg_le_neg_iff, neg_le, neg_zero],
      simp [ha], },
    { simp } },
end

lemma theta_zero_of_eval2_zero {S : Fintype} (c : ℝ≥0) {f : invpoly r S} (hf1 : eval2 p S f = 0) :
(laurent_measures.Θ p S) ((to_laurent_measures_addhom r S) f) = 0 :=
begin
  ext s,
  replace hf1 := congr_fun hf1 s,
  suffices : ∑' (n : ℤ), ↑(to_laurent_measures_fun «r» S f s n) * ((2 : ℝ) ^ n)⁻¹ = 0,
  { simpa [laurent_measures.Θ, laurent_measures_ses.θ_to_add, θ, theta.ϑ,
    to_laurent_measures_addhom], },
  simp only [theta_eval2_aux p s c, int.cast_eq_zero],
  exact hf1,
end
.

lemma _root_.int.eq_neg_nat_or_succ_nat (n : ℤ) : ∃ m : ℕ, n = -m ∨ n = m + 1 :=
begin
  cases le_or_lt n 0,
  { use n.nat_abs,
    left,
    rw [int.nat_abs_of_nonpos h, neg_neg] },
  { use (n - 1).nat_abs,
    right,
    rw [int.nat_abs_of_nonneg],
    ring, linarith },
end

lemma phi_eq_mul_Tinv_sub_two {S : Fintype} (g : invpoly r S) :
  ϕ ((to_laurent_measures_addhom r S) (λ (s : ↥S), g s)) =
    (to_laurent_measures_addhom r S) (λ (s : ↥S), (polynomial.X - 2) * g s) :=
begin
  ext s n,
  delta ϕ,
  simp only [laurent_measures.sub_apply, laurent_measures.shift_to_fun_to_fun,
    laurent_measures.nsmul_apply, nsmul_eq_mul, int.nat_cast_eq_coe_nat,
    int.coe_nat_zero, zero_add],
  obtain ⟨m, (rfl | rfl)⟩ := n.eq_neg_nat_or_succ_nat,
  { simp only [to_laurent_measures_addhom, to_laurent_measures_fun_nonpos, add_monoid_hom.mk'_apply,
      to_laurent_measures_to_fun],
    cases m,
    { simp only [nat.nat_zero_eq_zero, int.coe_nat_zero, neg_zero', zero_add,
        polynomial.mul_coeff_zero, polynomial.coeff_sub,
        polynomial.coeff_X_zero, zero_sub, neg_mul],
      rw [to_laurent_measures_fun_pos'' r S g s (show (0 : ℤ) < 1, by norm_num)],
      simp only [zero_sub, neg_inj, mul_eq_mul_right_iff,
        show (2 : polynomial ℤ) = polynomial.C 2, by simp, polynomial.coeff_C_zero],
      left,
      norm_num, },
    { simp only [to_laurent_measures_fun_nonpos, sub_mul, int.coe_nat_succ, neg_add_rev,
        neg_add_cancel_comm, int.coe_nat_bit0, int.coe_nat_zero, zero_add, polynomial.coeff_sub,
        polynomial.coeff_X_mul, sub_right_inj, show (2 : polynomial ℤ) = polynomial.C 2, by simp,
        polynomial.coeff_C_mul],
    } },
  { norm_cast }, -- didn't expect that to close it!
end

lemma psi_eq_div_X_sub_two {S : Fintype} (c : ℝ≥0) {f : invpoly r S}
  (hf1 : ((eval2_nat_trans p).app S) f = 0) :
(to_laurent_measures_addhom r S) (λ (s : ↥S), f s /ₘ (polynomial.X - 2)) =
  ψ ((to_laurent_measures_addhom «r» S) f) (theta_zero_of_eval2_zero p c hf1) :=
begin
  apply injective_ϕ',
  rw θ_ϕ_split_exact,
  have hf3 : ∀ s : S, (polynomial.X - 2) * ((f s) /ₘ (polynomial.X - 2)) = f s,
  { intro s,
    replace hf1 := congr_fun hf1 s,
    rw (show (2 : polynomial ℤ) = polynomial.C (2 : ℤ), by simp),
    rwa polynomial.mul_div_by_monic_eq_iff_is_root, },
  suffices : (to_laurent_measures_addhom r S)
    (λ s, (polynomial.X - 2) * ((f s) /ₘ (polynomial.X - 2))) =
    (to_laurent_measures_addhom r S) (λ s, f s),
  { rw ← this,
    apply phi_eq_mul_Tinv_sub_two, },
  simp [hf3],
end

theorem short_exact (S : Profinite) :
  short_exact ((condensify_Tinv2 _).app S) ((condensify_map $ eval2_nat_trans p).app S) :=
begin
  let κ : ℝ≥0 → ℝ≥0 := λ c, max c (c ^ (↑p⁻¹ : ℝ)),
  have hκ : id ≤ κ := λ c, le_max_left _ _,
  have h0p : 0 < p := fact.out _,
  have hp1 : p ≤ 1 := fact.out _,
  have h0pinv : 0 ≤ p⁻¹, { rw ← nnreal.inv_pos at h0p, exact h0p.le },
  refine condensify_nonstrict_exact _ _ (r⁻¹ + 2) (Tinv2_bound_by _)
    -- next line can be simplified because 1/2 < r < 1 so the max is always on the right.
    (λ c, max c (c * (2 - r⁻¹)⁻¹ * (r⁻¹ + 2))) κ
    (λ c, le_max_left _ _) hκ
    (Tinv2_injective p) (Tinv2_comp_eval2_eq_zero p) _ _ _,
  { rintros S c f ⟨hf1, hf2⟩,
    have hf3 : ∀ s : S, (polynomial.X - 2) * ((f s) /ₘ (polynomial.X - 2)) = f s,
    { intro s,
      replace hf1 := congr_fun hf1 s,
      rw (show (2 : polynomial ℤ) = polynomial.C (2 : ℤ), by simp),
      rwa polynomial.mul_div_by_monic_eq_iff_is_root, },
    refine ⟨λ s, (f s) /ₘ (polynomial.X - 2), _, _⟩,
    { change ∥_∥₊ ≤ c at hf2,
      change ∥_∥₊ ≤ _,
      have hf1' : ((eval2_nat_trans p).app S) f = 0,
      { simpa using hf1 },
      rw ← to_laurent_measures_addhom_isometry at ⊢ hf2,
      refine le_trans _ (nnreal.mul_le_mul_right (le_max_right _ _) _),
      rw mul_inv_cancel_right₀ (lt_of_lt_of_le (zero_lt_two : (0 : ℝ≥0) < 2) le_add_self).ne',
      convert laurent_measures.psi_bound p S c (theta_zero_of_eval2_zero p c hf1') hf2,
      exact psi_eq_div_X_sub_two p c hf1,
    },
    { ext1 s,
      convert hf3 s,
      simp [sub_mul, Tinv2_nat_trans, Tinv_nat_trans],
      refl } },
  { rintro S c g (hg : _ ≤ _),
    let f : invpoly r S := λ s, polynomial.C (g s),
    refine ⟨f, _, _⟩,
    { show _ ≤ _,
      replace hg := nnreal.rpow_le_rpow hg h0pinv,
      refine le_trans _ (le_max_right _ _),
      refine le_trans _ hg,
      refine le_trans _ (nnreal.rpow_le_rpow (nnreal.rpow_sum_le_sum_rpow _ _ h0p hp1) h0pinv),
      rw [← nnreal.rpow_mul, ← nnreal.coe_mul, mul_inv_cancel h0p.ne', nnreal.coe_one,
        nnreal.rpow_one, invpoly.nnnorm_def],
      refine finset.sum_le_sum _,
      rintro s -,
      simp only [f, zpow_neg₀, zpow_coe_nat, id.def, polynomial.coeff_C],
      rw tsum_eq_single 0,
      { rw [if_pos rfl, pow_zero, inv_one, mul_one], },
      { intros n hn, rw [if_neg hn, nnnorm_zero, zero_mul], },
      { apply_instance }, },
    { ext s, apply polynomial.eval_C } },
end

end ses

end invpoly
