import free_pfpng.main
import invpoly.functor
import condensed.condensify
import laurent_measures.thm69
import normed_free_pfpng.compare

universe u

noncomputable theory

open category_theory

open_locale nnreal big_operators

namespace invpoly
open ProFiltPseuNormGrpWithTinv₁

variables (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)]

local notation `r` := @r p

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

-- move this
@[simp] lemma _root_.comphaus_filtered_pseudo_normed_group_hom.sub_apply {M N : Type*}
  [comphaus_filtered_pseudo_normed_group M] [comphaus_filtered_pseudo_normed_group N]
  (f g : comphaus_filtered_pseudo_normed_group_hom M N) (x : M) :
  (f - g) x = f x - g x := rfl

-- move this
@[simp] lemma _root_.comphaus_filtered_pseudo_normed_group_hom.nsmul_apply {M N : Type*}
  [comphaus_filtered_pseudo_normed_group M] [comphaus_filtered_pseudo_normed_group N]
  (n : ℕ) (f : comphaus_filtered_pseudo_normed_group_hom M N) (x : M) :
  (n • f) x = n • (f x) := rfl

@[simp] lemma _root_.comphaus_filtered_pseudo_normed_group_hom.zero_apply (M N : Type*)
  [comphaus_filtered_pseudo_normed_group M] [comphaus_filtered_pseudo_normed_group N]
  (x : M) :
  (0 : comphaus_filtered_pseudo_normed_group_hom M N) x = 0 := rfl

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
    (whisker_right (eval2_nat_trans p) enlarging_functor).app S = 0 :=
begin
  ext f s,
  show (polynomial.X * (f s) - _).eval 2 = (0 : ℤ),
  simp only [nat_trans.app_nsmul, nat_trans.id_app, comphaus_filtered_pseudo_normed_group_hom.nsmul_apply,
  category_theory.id_apply, pi.smul_apply, nsmul_eq_mul, nat.cast_bit0, nat.cast_one, polynomial.eval_sub,
  polynomial.eval_mul, polynomial.eval_X, polynomial.eval_bit0, polynomial.eval_one, sub_self],
end

theorem short_exact (S : Profinite) :
  short_exact ((condensify_Tinv2 _).app S) ((condensify_map $ eval2_nat_trans p).app S) :=
begin
  let κ : ℝ≥0 → ℝ≥0 := λ c, max c (c ^ (↑p⁻¹ : ℝ)),
  have hκ : id ≤ κ := λ c, le_max_left _ _,
  have h0p : 0 < p := fact.out _,
  have hp1 : p ≤ 1 := fact.out _,
  have h0pinv : 0 ≤ p⁻¹, { rw ← nnreal.inv_pos at h0p, exact h0p.le },
  refine condensify_nonstrict_exact _ _ (r⁻¹ + 2) (Tinv2_bound_by _) _ κ _ hκ
    (Tinv2_injective p) (Tinv2_comp_eval2_eq_zero p) _ _ _,
  swap 4,
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
  all_goals { sorry },
end

end ses

end invpoly
