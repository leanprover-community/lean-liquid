-- import laurent_measures.functor
import laurent_measures.thm69
-- import data.real.basic

/-
This files introduces the maps `Θ`, `Φ` (***and `Ψ` ???***), which are the "measurifications" of `θ`, `ϕ` (*** and `ψ` ???***)
`laurent_measures.thm69`, they are morphisms in the right category.

We then prove in **???** that `θ_ϕ_exact` of `laurent_measures.thm69` becomes a short exact sequence
in the category **???**.
-/


noncomputable theory

universe u

namespace laurent_measures_ses

open laurent_measures pseudo_normed_group comphaus_filtered_pseudo_normed_group comphaus_filtered_pseudo_normed_group_hom
open_locale big_operators nnreal

section homs

parameter {p : ℝ≥0}

def r : ℝ≥0 := (1 / 2) ^ (p:ℝ)

lemma r_coe : (1 / 2 : ℝ) ^ (p : ℝ) = (r : ℝ) :=
begin
  have : (1/2 : ℝ) = ((1/2 : ℝ≥0) : ℝ),
  simp only [one_div, nonneg.coe_inv, nnreal.coe_bit0, nonneg.coe_one],
  rw [this, ← nnreal.coe_rpow, nnreal.coe_eq],
  refl,
end

variables [fact(0 < p)] [fact (p < 1)]
variables [fact (0 < r)] --not nice, turn it into an instance
variable {S : Fintype}

local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

variables {M₁ M₂ : Type u} [comphaus_filtered_pseudo_normed_group M₁] [comphaus_filtered_pseudo_normed_group M₂]

def cfpng_hom_add (f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) : (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
begin
  apply mk_of_bound (f.to_add_monoid_hom + g.to_add_monoid_hom) (f.bound.some + g.bound.some),
  intro c,
  refine ⟨_, _⟩,
  { intros x hx,
      simp only [comphaus_filtered_pseudo_normed_group_hom.coe_mk],
      simp only [add_monoid_hom.add_apply, coe_to_add_monoid_hom],
      convert pseudo_normed_group.add_mem_filtration (f.bound.some_spec hx) (g.bound.some_spec hx),
      rw add_mul, },
  let f₀ : filtration M₁ c → filtration M₂ (f.bound.some * c) := λ x, ⟨f x, f.bound.some_spec x.2⟩,
  have hf₀ : continuous f₀ := f.continuous _ (λ x, rfl),
  let g₀ : filtration M₁ c → filtration M₂ (g.bound.some * c) := λ x, ⟨g x, g.bound.some_spec x.2⟩,
  have hg₀ : continuous g₀ := g.continuous _ (λ x, rfl),
  simp only [add_monoid_hom.add_apply, coe_to_add_monoid_hom],
  haveI : fact ((f.bound.some * c + g.bound.some * c) ≤ ((f.bound.some + g.bound.some) * c) ) := fact.mk (le_of_eq (add_mul _ _ _).symm),
  let ι : filtration M₂ (f.bound.some * c + g.bound.some * c) → filtration M₂ ((f.bound.some + g.bound.some) * c) := cast_le,
  have hι : continuous ι := continuous_cast_le _ _,
  let S₀ : filtration M₂ (f.bound.some * c) × filtration M₂ (g.bound.some * c) → filtration M₂ (f.bound.some * c + g.bound.some * c) := λ x, ⟨x.fst + x.snd, add_mem_filtration x.fst.2 x.snd.2⟩,
  have hS₀ := continuous_add' (f.bound.some * c) (g.bound.some * c),
  exact hι.comp (hS₀.comp (continuous.prod_mk hf₀ hg₀)),
end

def cfpng_hom_neg (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) : (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
begin
  apply mk_of_bound (- f.to_add_monoid_hom) (f.bound.some),
  intro c,
  refine ⟨_, _⟩,
  { intros x hx,
    simp only [comphaus_filtered_pseudo_normed_group_hom.coe_mk],
    convert pseudo_normed_group.neg_mem_filtration (f.bound.some_spec hx) },
  let f₀ : filtration M₁ c → filtration M₂ (f.bound.some * c) := λ x, ⟨f x, f.bound.some_spec x.2⟩,
  have hf₀ : continuous f₀ := f.continuous _ (λ x, rfl),
  exact (continuous_neg' _).comp hf₀,
end

instance : add_comm_group (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
{ add := cfpng_hom_add,
  add_assoc := by {intros, ext, apply add_assoc},
  zero := 0,
  zero_add := by {intros, ext, apply zero_add},
  add_zero := by {intros, ext, apply add_zero},
  neg := cfpng_hom_neg,
  add_left_neg := by {intros, ext, apply add_left_neg},
  add_comm := by {intros, ext, apply add_comm} }

def Φ : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) := 2 • shift (-1) - id

lemma Φ_eq_ϕ (F : ℒ S) : Φ F = ϕ F := rfl

section theta

lemma θ_zero : θ (0 : ℒ S) = 0 :=
begin
  dsimp only [θ, theta.ϑ],
  funext,
  simp only [zero_apply, int.cast_zero, zero_mul, tsum_zero, real_measures.zero_apply],
end

lemma θ_add (F G : ℒ S) : θ (F + G) = θ F + θ G :=
begin
  dsimp only [θ, theta.ϑ],
  funext,
  simp only [laurent_measures.add_apply, int.cast_add, one_div, inv_zpow', zpow_neg₀, real_measures.add_apply, tsum_add],
  rw ← tsum_add,
  { congr,
    funext,
    rw add_mul },
  all_goals {apply summable_of_summable_norm, simp_rw [normed_field.norm_mul, normed_field.norm_inv, normed_field.norm_zpow, real.norm_two, ← inv_zpow₀, inv_eq_one_div] },
  exact aux_thm69.summable_smaller_radius_norm F.d r_half (F.summable s) (lt_d_eq_zero _ _),
  exact aux_thm69.summable_smaller_radius_norm G.d r_half (G.summable s) (lt_d_eq_zero _ _),
end

example (a : ℤ) (ha : a ≠ 0) : 1 ≤ |a| :=
begin
  rw int.abs_eq_nat_abs,
  rw ← nat.cast_one,
  apply int.coe_nat_le_coe_nat_of_le,
  rw zero_add,
  rw nat.one_le_iff_ne_zero,
  rw ne.def,
  rwa int.nat_abs_eq_zero,
end



lemma θ_bound : ∃ C, ∀ c : ℝ≥0, ∀ F : (ℒ S), F ∈ filtration (ℒ S) c → (θ F) ∈ filtration (ℳ S)
  (C * c) :=
begin
    have h_two : 0 ≤ (2 : ℝ)⁻¹ , sorry,
    use 1,
    intros c F hF,
    rw one_mul,
    rw mem_filtration_iff at hF,
    dsimp only [laurent_measures.has_nnnorm] at hF,
    rw real_measures.mem_filtration_iff,
    dsimp only [real_measures.has_nnnorm, θ, theta.ϑ],
    let T := S.2.1,
    -- convert_to ∑ s in T, ∥∑' (n : ℤ), ((F s n) : ℝ) * (1 / 2) ^ n∥₊ ^ (p : ℝ) ≤ c,
    have ineq : ∀ (s ∈ T), ∥∑' (n : ℤ), ((F s n) : ℝ) * (1 / 2) ^ n∥₊ ^ (p : ℝ) ≤ ∑' (n : ℤ),
      ∥ ((F s n) : ℝ) * (1 / 2) ^ n∥₊ ^ (p : ℝ), sorry,
    apply (finset.sum_le_sum ineq).trans,
    simp_rw [normed_field.nnnorm_mul, ← inv_eq_one_div, normed_field.nnnorm_zpow,
     normed_field.nnnorm_inv, nnreal.mul_rpow, real.nnnorm_two, ← nnreal.coe_le_coe, nnreal.coe_sum,
     nnreal.coe_tsum, nnreal.coe_mul, nnreal.coe_rpow, nnreal.coe_zpow, nnreal.coe_inv],
    simp only [_root_.coe_nnnorm, nnreal.coe_bit0, nonneg.coe_one],
    simp_rw [← real.rpow_int_cast, ← real.rpow_mul h_two, mul_comm _ (p : ℝ), real.rpow_mul h_two,
      inv_eq_one_div, r_coe],
    --put together all the `simp_rw` above
    simp_rw [← nnreal.coe_le_coe] at hF,
    simp_rw nnreal.coe_sum at hF,
    simp_rw nnreal.coe_tsum at hF,
    simp_rw nnreal.coe_mul at hF,
    simp_rw nnreal.coe_zpow at hF,
    simp only [_root_.coe_nnnorm] at hF,
    apply le_trans _ hF,
    apply finset.sum_le_sum,
    intros s hs,
    apply tsum_le_tsum,
    { intro b,
      rw real.rpow_int_cast,
      apply ordered_ring.mul_le_mul_of_nonneg_right,
      -- rw cast_int
      have p_le_one : (p : ℝ) ≤ 1,
      { apply le_of_lt,
        rw [← nnreal.coe_one, nnreal.coe_lt_coe],
        exact fact.out _, },
      by_cases hF_nz : F s b = 0,
      { rw [hF_nz, int.cast_zero, norm_zero, norm_zero, real.zero_rpow],
        rw [ne.def, ← nnreal.coe_zero, nnreal.coe_eq, ← ne.def],
        exact ne_of_gt (fact.out _) },
      convert real.rpow_le_rpow_of_exponent_le _ p_le_one,
      { rw real.rpow_one, refl },
      { rw real.norm_eq_abs,
        sorry,
        -- have : ((|F s b| : ℤ) : ℝ) = |(F s b : ℝ)|,


        -- rw this,
        -- rw real.coe_abs
        -- rw int.abs_eq_nat_abs,
        -- rw ← nat.cast_one,
        -- apply int.coe_nat_le_coe_nat_of_le,
        -- rw zero_add,
        -- rw nat.one_le_iff_ne_zero,
        -- rw ne.def,
        -- rwa int.nat_abs_eq_zero,
        -- -- apply le_one_nonz
        -- squeeze_simp,
        -- rw real.abs_one,
        -- rw ← real.norm_coe_nat,

      },sorry,

      -- _ _,-- _ ((r : ℝ) ^ (b : ℝ)),
      -- refine (mul_le_mul_iff_right ((r : ℝ) ^ (b : ℝ))).mpr,
      },
      sorry,

end

-- lemma θ_continuous (F G : ℒ S) : θ (F + G) = θ F + θ G := sorry

def Θ : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℳ S) :=
{ to_fun := λ F, θ F,
  map_zero' := θ_zero,
  map_add' := θ_add,
  bound' := θ_bound,
  -- end,
  continuous' := sorry }



end theta

end homs

end laurent_measures_ses
