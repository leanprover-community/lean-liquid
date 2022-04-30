-- import laurent_measures.functor
import analysis.special_functions.logb
import for_mathlib.pi_induced
import laurent_measures.thm69
-- import data.real.basic

/-
This files introduces the maps `Θ`, `Φ` (***and `Ψ` ???***), which are the "measurifications" of
`θ`, `ϕ` (*** and `ψ` ???***)
`laurent_measures.thm69`, they are morphisms in the right category.

We then prove in **???** that `θ_ϕ_exact` of `laurent_measures.thm69` becomes a short exact sequence
in the category **???**.
-/


noncomputable theory

universe u

namespace laurent_measures_ses

open laurent_measures pseudo_normed_group comphaus_filtered_pseudo_normed_group
open comphaus_filtered_pseudo_normed_group_hom
open_locale big_operators nnreal

section phi_to_hom

-- parameter {p : ℝ≥0}
-- variables [fact(0 < p)] [fact (p < 1)]
-- local notation `r` := @r p
-- local notation `ℳ` := real_measures p

variable {r : ℝ≥0}
variables [fact (0 < r)]
variable {S : Fintype}

local notation `ℒ` := laurent_measures r
local notation `ϖ` := (Fintype.of punit : Type u)

variables {M₁ M₂ : Type u} [comphaus_filtered_pseudo_normed_group M₁]
  [comphaus_filtered_pseudo_normed_group M₂]

def cfpng_hom_add (f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
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
  haveI : fact ((f.bound.some * c + g.bound.some * c) ≤ ((f.bound.some + g.bound.some) * c) ) :=
    fact.mk (le_of_eq (add_mul _ _ _).symm),
  let ι : filtration M₂ (f.bound.some * c + g.bound.some * c) → filtration M₂
    ((f.bound.some + g.bound.some) * c) := cast_le,
  have hι : continuous ι := continuous_cast_le _ _,
  let S₀ : filtration M₂ (f.bound.some * c) × filtration M₂ (g.bound.some * c) →
    filtration M₂ (f.bound.some * c + g.bound.some * c) :=
      λ x, ⟨x.fst + x.snd, add_mem_filtration x.fst.2 x.snd.2⟩,
  have hS₀ := continuous_add' (f.bound.some * c) (g.bound.some * c),
  exact hι.comp (hS₀.comp (continuous.prod_mk hf₀ hg₀)),
end

def cfpng_hom_neg (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
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

variable (S)

/-- The map on Laurent measures induced by multiplication by `T⁻¹ - 2` on `ℤ((T))ᵣ`. -/
def Φ : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) := shift (1) - 2 • id
-- variable {S}


lemma Φ_eq_ϕ (F : ℒ S) : Φ S F = ϕ F := rfl

-- after the Φ refactor the below lemma is no longer true

-- lemma Φ_bound_by_3 [fact (r ≤ 1)] :
--   (Φ S : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S)).bound_by 3 :=
-- begin
--   let sh : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) := shift (-1),
--   let shup : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) := shift (1),
--   have Hsh : sh.bound_by 1,
--   { refine (mk_of_bound_bound_by _ _ _).mono 1 _,
--     rw [neg_neg], exact (pow_one r).le.trans (fact.out _) },
--   have Hshup : shup.bound_by 1,
--   { refine (mk_of_bound_bound_by _ _ _).mono (1) _,

--   }
--   suffices : (sh + sh + (-id)).bound_by (1 + 1 + 1),
--   { convert this using 1, ext1, dsimp only [Φ_eq_ϕ, ϕ], erw two_nsmul, }, -- was refl
--   refine (Hsh.add Hsh).add (mk_of_bound_bound_by _ _ _).neg,
-- end

lemma Φ_natural (S T : Fintype) (f : S ⟶ T) (F : ℒ S) (t : T) (n : ℤ) :
  Φ T (map f F) t n = laurent_measures.map f (Φ S F) t n :=
begin
  simp [Φ_eq_ϕ, ϕ, finset.mul_sum],
end

end phi_to_hom

section theta

open theta real_measures

parameter (p : ℝ≥0)
local notation `r` := @r p
local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

variable {S : Fintype.{u}}

local notation `ϖ` := Fintype.of (punit : Type u)

def seval_ℒ_c (c : ℝ≥0) (s : S) : filtration (ℒ S) c → (filtration (ℒ ϖ) c) :=
λ F,
begin
  refine ⟨seval_ℒ S s F, _⟩,
  have hF := F.2,
  simp only [filtration, set.mem_set_of_eq, seval_ℒ, nnnorm, laurent_measures.coe_mk,
    fintype.univ_punit, finset.sum_singleton] at ⊢ hF,
  have := finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr $ finset.mem_univ_val _),
  rw finset.sum_singleton at this,
  apply le_trans this hF,
end

variable [fact (0 < p)]

lemma θ_zero : θ (0 : ℒ S) = 0 :=
begin
  dsimp only [θ, theta.ϑ],
  funext,
  simp only [laurent_measures.zero_apply, int.cast_zero, zero_mul, tsum_zero, real_measures.zero_apply],
end

variable [fact (p < 1)]

lemma θ_add (F G : ℒ S) : θ (F + G) = θ F + θ G :=
begin
  dsimp only [θ, theta.ϑ],
  funext,
  simp only [laurent_measures.add_apply, int.cast_add, one_div, inv_zpow', zpow_neg₀, real_measures.add_apply, tsum_add],
  rw ← tsum_add,
  { congr,
    funext,
    rw add_mul },
  all_goals {apply summable_of_summable_norm, simp_rw [norm_mul, norm_inv, norm_zpow, real.norm_two,
    ← inv_zpow₀, inv_eq_one_div] },
  exact aux_thm69.summable_smaller_radius_norm F.d half_lt_r (F.summable s) (λ n, lt_d_eq_zero _ _ _),
  exact aux_thm69.summable_smaller_radius_norm G.d half_lt_r (G.summable s) (λ n, lt_d_eq_zero _ _ _),
end

--for mathlib
lemma nnreal.rpow_int_cast (x : ℝ≥0) (n : ℤ) : x ^ n = x ^ (n : ℝ) := by {
  rw [← nnreal.coe_eq, nnreal.coe_zpow, ← real.rpow_int_cast, ← nnreal.coe_rpow] }

lemma nnreal.rpow_le_rpow_of_exponent_le {x : ℝ≥0} (x1 : 1 ≤ x) {y z : ℝ}
  (hyz : y ≤ z) :
  x ^ y ≤ x ^ z :=
by { cases x with x hx, exact real.rpow_le_rpow_of_exponent_le x1 hyz }

lemma nnreal.tsum_geom_arit_inequality (f: ℤ → ℝ) {r' : ℝ} (hr'1 : 0 < r') (hr'2 : r' ≤ 1)
  (hs1 : summable (λ n, f n)) (hs2 : summable (λ n, ∥(f n)∥₊ ^ r')) :
  ∥ tsum (λ n, f n) ∥₊ ^ r' ≤ tsum (λ n, ∥(f n)∥₊ ^ r' ) :=
begin
  rw ← summable_norm_iff at hs1,
  simp_rw ← _root_.coe_nnnorm at hs1,
  rw nnreal.summable_coe at hs1,
  refine le_trans (nnreal.rpow_le_rpow (nnnorm_tsum_le hs1) hr'1.le) _,
  have := λ s : finset ℤ, nnreal.rpow_sum_le_sum_rpow s (λ i, ∥f i∥₊) hr'1 hr'2,
  dsimp only at this,
  have s1' := filter.tendsto.comp (continuous.tendsto
    (nnreal.continuous_rpow_const hr'1.le) _) hs1.has_sum,
  dsimp [function.comp] at s1',
  apply tendsto_le_of_eventually_le s1' hs2.has_sum,
  delta filter.eventually_le,
  convert filter.univ_sets _,
  ext x,
  simp [this],
end


lemma aux_bound (F : ℒ S) (s : S) : ∀ (b : ℤ), ∥(F s b : ℝ) ∥₊ ^ (p : ℝ) *
  (2⁻¹ ^ (p : ℝ)) ^ (b : ℝ) ≤ ∥F s b∥₊ * r ^ b :=
begin
  intro b,
  rw [inv_eq_one_div, nnreal.rpow_int_cast],
  refine mul_le_mul_of_nonneg_right _ (real.rpow_nonneg_of_nonneg (nnreal.coe_nonneg _) _),
  have p_le_one : (p : ℝ) ≤ 1,
  { rw ← nnreal.coe_one,
    exact (nnreal.coe_lt_coe.mpr $ fact.out _).le },
  by_cases hF_nz : F s b = 0,
  { rw [hF_nz, int.cast_zero, nnnorm_zero, nnnorm_zero, nnreal.zero_rpow],
    rw [ne.def, ← nnreal.coe_zero, nnreal.coe_eq, ← ne.def],
    exact ne_of_gt (fact.out _) },
  { convert nnreal.rpow_le_rpow_of_exponent_le _ p_le_one,
    { rw nnreal.rpow_one,
      refl },
    { refine not_lt.mp (λ hf, hF_nz (int.abs_lt_one_iff.mp _)),
      suffices : (|F s b| : ℝ) < 1, exact_mod_cast this,
      rw ← int.norm_eq_abs,
      rwa [← nnreal.coe_lt_coe, ← nnnorm_norm, real.nnnorm_of_nonneg (norm_nonneg _)] at hf } }
end

lemma θ_bound : ∀ c : ℝ≥0, ∀ F : (ℒ S), F ∈ filtration (ℒ S) c → (θ F) ∈ filtration (ℳ S)
  (1 * c) :=
begin
  intros c F hF,
  rw laurent_measures.mem_filtration_iff at hF,
  dsimp only [laurent_measures.has_nnnorm] at hF,
  rw [one_mul, real_measures.mem_filtration_iff],
  dsimp only [real_measures.has_nnnorm, θ, theta.ϑ],
  let T := S.2.1,
  have ineq : ∀ (s ∈ T), ∥∑' (n : ℤ), ((F s n) : ℝ) * (2⁻¹) ^ n∥₊ ^ (p : ℝ) ≤ ∑' (n : ℤ),
    ∥ ((F s n) : ℝ) * (2⁻¹) ^ n∥₊ ^ (p : ℝ),
  { intros s hs,
    apply nnreal.tsum_geom_arit_inequality (λ n, ((F s n) * (2⁻¹) ^ n)),
    { norm_num, exact fact.out _},
    { suffices : p ≤ 1, assumption_mod_cast, exact fact.out _},
    { dsimp only,
      obtain ⟨d, hd⟩ := exists_bdd_filtration (r_pos) (r_lt_one) F,
      apply aux_thm69.summable_smaller_radius d (F.summable s) (hd s) half_lt_r },
    { dsimp only,
      simp_rw [nnnorm_mul, nnreal.mul_rpow],
      have := F.summable s,
      rw ← nnreal.summable_coe,
      apply summable_of_nonneg_of_le (λ i, _) _ this, apply nnreal.zero_le_coe,
      intro n,
      push_cast,
      apply mul_le_mul,
      { -- true because ∥integer∥ is either 0 or >= 1
        norm_cast,
        by_cases h : F s n = 0,
        { simp only [h, norm_zero],
          refine le_of_eq (real.zero_rpow _),
          norm_cast,
          exact ne_of_gt (fact.out _) },
        { nth_rewrite 1 (real.rpow_one (∥F s n∥)).symm,
          apply real.rpow_le_rpow_of_exponent_le,
          { rw [int.norm_eq_abs, le_abs'],
            norm_cast,
            rcases lt_trichotomy 0 (F s n) with (hF|hF|hF),
            { right, linarith },
            { exact false.elim (h hF.symm) },
            { left, change _ ≤ -(1 : ℤ), linarith, } },
          { norm_cast, exact fact.out _ } } },
      { apply le_of_eq,
        rw [← r_coe],
        rw real.norm_of_nonneg,
        { -- can't use pow_mul yet because one is int one is real
          rw [← real.rpow_int_cast, ← real.rpow_int_cast],
          rw [← real.rpow_mul, mul_comm, real.rpow_mul];
          norm_num },
        { apply zpow_nonneg,
          norm_num } },
      { refine (real.rpow_pos_of_pos _ _).le,
        rw norm_pos_iff,
        apply zpow_ne_zero,
        norm_num, },
      { apply norm_nonneg, } } },
  apply (finset.sum_le_sum ineq).trans,
  simp_rw [nnnorm_mul, ← inv_eq_one_div, nnnorm_zpow, nnnorm_inv, nnreal.mul_rpow, real.nnnorm_two,
    nnreal.rpow_int_cast, ← nnreal.rpow_mul (2 : ℝ≥0)⁻¹, mul_comm, nnreal.rpow_mul (2 : ℝ≥0)⁻¹],
  apply le_trans _ hF,
  apply finset.sum_le_sum,
  intros s hs,
  apply tsum_le_tsum,
  exact aux_bound p F s,
  refine nnreal.summable_of_le _ (F.2 s),
  exacts [aux_bound p F s, F.2 s],
end


lemma θ_bound' :  ∀ c : ℝ≥0, ∀ F : (ℒ S), F ∈ filtration (ℒ S) c → (θ F) ∈ filtration (ℳ S)
  c :=by { simpa [one_mul] using (θ_bound p)}

def θ_to_add : (ℒ S) →+ (ℳ S) :=
{ to_fun := λ F, θ F,
  map_zero' := θ_zero,
  map_add' := θ_add, }

variable (S)

open theta metric real_measures

def seval_ℳ_c (c : ℝ≥0) (s : S) : filtration (ℳ S) c → (filtration (ℳ ϖ) c) :=
λ x,
  begin
  refine ⟨(λ _, x.1 s), _⟩,
  have hx := x.2,
  simp only [filtration, set.mem_set_of_eq, nnnorm, laurent_measures.coe_mk,
    fintype.univ_punit, finset.sum_singleton] at ⊢ hx,
  have := finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr $ finset.mem_univ_val _),
  rw finset.sum_singleton at this,
  apply le_trans this hx,
end

-- **[FAE]** From here everything might be useless until `lemma inducing_cast_ℳ`: check
-- also the `variable (c : ℝ≥0)` issue; the idea is to replace cast_ℳ_c with α, for which
-- everything seems to work

variable (c : ℝ≥0)

def box := {F : (ℳ S) // ∀ s, ∥ F s ∥₊ ^ (p : ℝ) ≤ c }

instance : has_coe (box S c) (ℳ S) := by {dsimp only [box], apply_instance}
instance : topological_space (ℳ S) := by {dsimp only [real_measures], apply_instance}
instance : topological_space (box S c) := by {dsimp only [box], apply_instance}


def equiv_box_ϖ : (box S c) ≃ Π (s : S), (filtration (ℳ ϖ) c) :=
begin
  fconstructor,
  { intros F s,
    use seval_ℳ S s F.1,
    simp only [real_measures.mem_filtration_iff, nnnorm, fintype.univ_punit,
      finset.sum_singleton, seval_ℳ],
    exact F.2 s },
  { intro G,
    use λ s, (G s).1 punit.star,
    intro s,
    simpa only [real_measures.mem_filtration_iff, nnnorm, fintype.univ_punit,
      finset.sum_singleton, seval_ℳ] using (G s).2 },
  { intro _,
    ext s,
    simpa only [seval_ℳ] },
  { intro G,
    ext s,
    simp only [seval_ℳ, subtype.val_eq_coe, subtype.coe_mk],
    induction x,
    refl }
end

def homeo_box_ϖ : (box S c) ≃ₜ Π (s : S), (filtration (ℳ ϖ) c) :=
{ to_equiv := equiv_box_ϖ S c,
  continuous_to_fun := begin
    apply continuous_pi,
    intro s,
    dsimp only [equiv_box_ϖ, seval_ℳ],
    refine continuous_subtype_mk (λ (x : box p S c), equiv_box_ϖ._proof_3 p S c x s)
      (continuous_pi (λ (i : ↥(Fintype.of punit)), _)),
    exact continuous_pi_iff.mp continuous_induced_dom s,
  end,
  continuous_inv_fun :=
  begin
    dsimp only [equiv_box_ϖ, seval_ℳ],
    refine continuous_subtype_mk (λ (x : ↥S → ↥(filtration (real_measures p (Fintype.of punit)) c)),
      equiv_box_ϖ._proof_4 p S c x) _,
    apply continuous_pi,
    intro s,
    have h : continuous (λ (a : S → (filtration (ℳ ϖ) c)), (a s).val)
       := continuous.subtype_coe (continuous_apply s),
    have H := continuous_apply punit.star,
    exact H.comp h,
  end}


def α : filtration (ℳ S) c → box S c :=
begin
  intro x,
  use x,
  have hx := x.2,
  intro s,
  simp only [filtration, set.mem_set_of_eq, nnnorm, laurent_measures.coe_mk,
    fintype.univ_punit, finset.sum_singleton] at hx,
  have := finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr $ finset.mem_univ_val _),
  rw finset.sum_singleton at this,
  apply le_trans this hx,
end


lemma coe_α_coe : (coe : (box S c) → (ℳ S)) ∘ (α S c) = coe := by {funext _, refl}

lemma inducing_α : inducing (α S c) :=
begin
  have ind_ind := @induced_compose _ _ (ℳ S) _ (α p S c) coe,
  rw [coe_α_coe p S c] at ind_ind,
  exact {induced := eq.symm ind_ind},
end


lemma seval_ℳ_α_commute (c : ℝ≥0) (s : S) :
 (λ F, ((homeo_box_ϖ S c) ∘ (α S c)) F s) = (λ F, seval_ℳ_c S c s F) := rfl

 lemma seval_ℳ_α_commute' {X : Type*} (c : ℝ≥0) {f : X → filtration (ℳ S) c} (s : S)  :
 (λ x, ((homeo_box_ϖ S c) ∘ (α S c)) (f x) s) = (λ x, seval_ℳ_c S c s (f x)) :=
 begin
  ext z,
  have h_commute := @seval_ℳ_α_commute p S _ _ c s,
  have := congr_fun h_commute (f z),
  simp only at this,
  rw this,
 end

@[nolint unused_arguments]
def seval_ℒ_bdd_c (c : ℝ≥0) (S : Fintype) (A : finset ℤ) (s : S) :
laurent_measures_bdd r S A c → laurent_measures_bdd r ϖ A c :=
begin
  intro F,
  use λ _, F s,
  have hF := F.2,
  simp only [filtration, set.mem_set_of_eq, seval_ℒ, nnnorm, laurent_measures.coe_mk,
    fintype.univ_punit, finset.sum_singleton] at ⊢ hF,
  have := finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr $ finset.mem_univ_val _),
  rw finset.sum_singleton at this,
  apply le_trans this hF,
end

lemma continuous_seval_ℒ_c (c : ℝ≥0) (s : S) : continuous (seval_ℒ_c c s) :=
begin
  rw laurent_measures.continuous_iff,
  intro A,
  let := seval_ℒ_bdd_c p c S A s,
  have h_trunc : (@truncate r ϖ c A) ∘ (seval_ℒ_c p c s) =
    (seval_ℒ_bdd_c p c S A s) ∘ (@truncate r S c A),
  { ext ⟨F, hF⟩ π k,
    dsimp only [seval_ℒ_bdd_c, seval_ℒ_c],
    refl },
  rw h_trunc,
  apply continuous.comp,
  apply continuous_of_discrete_topology,
  apply truncate_continuous,
end

section topological_generalities

open metric set

variables {X : Type*} [topological_space X]

lemma reduction_balls {c : ℝ≥0} (f : X → (closed_ball (0 : ℝ) c)) (H : ∀ y : (closed_ball 0 c),
  ∀ ε : ℝ, is_open (f⁻¹' (ball y ε))) : continuous f :=
begin
  rw continuous_def,
  intros _ hU,
  rw is_open_iff_forall_mem_open,
  intros x hx,
  obtain ⟨ε, h₀, hε⟩ := (is_open_iff.mp hU) (f x) (mem_preimage.mp hx),
  use f⁻¹' (ball (f x) ε),
  exact ⟨preimage_mono hε, H (f x) ε, mem_ball_self h₀⟩,
end

lemma mem_filtration_le_monomial (F : filtration (ℒ ϖ) c) (n : ℕ) :
 ∥ ((F.1 punit.star n) : ℝ) ∥ ≤ c * ( 1 / r ^ n) :=
begin
  have h_le : ∑' n : ℤ, ∥ ((F.1 punit.star n) : ℝ) ∥ * r ^ n ≤ c,
  { have := (laurent_measures.mem_filtration_iff F.1 c).mp F.2,
    rw laurent_measures.nnnorm_def at this,
    simp only [fintype.univ_punit, finset.sum_singleton, ← nnreal.coe_le_coe,
    nnreal.coe_tsum, nnreal.coe_mul, nnreal.coe_zpow, laurent_measures.coe_nnnorm] at this,
    exact this },
  have := @sum_le_tsum ℝ _ _ _ _ (λ n, ∥ ((F.1 punit.star n) : ℝ) ∥ * r ^ n) {n} _
    (F.1.summable punit.star),
  simp only [finset.sum_singleton, zpow_coe_nat] at this,
  replace h_le := this.trans h_le,
  rwa [← inv_eq_one_div, ← inv_mul_le_iff', inv_inv ((r : ℝ) ^ n), mul_comm],
  { exact (inv_pos.mpr (pow_pos (nnreal.coe_pos.mpr r_pos) _)) },
  { rintros b -,
    simp only [subtype.val_eq_coe],
    exact mul_nonneg (norm_nonneg _) (zpow_nonneg (le_of_lt (nnreal.coe_pos.mpr r_pos)) b) },
end


lemma mem_filtration_sum_le_geom (F : filtration (ℒ ϖ) c) (B : ℕ) : ∥ ∑' n : {x : ℕ // B ≤ x},
  ((F.1 punit.star n) : ℝ) * (2⁻¹) ^ n.1 ∥ ≤ ∥ (c : ℝ) * ∑' n : {x : ℕ // B ≤ x}, (2⁻¹ * r⁻¹) ^ n.1 ∥ :=
begin
  have two_r_nonneg : 0 ≤ (2⁻¹ * r⁻¹ : ℝ) := by {apply one_div_nonneg.mpr (mul_nonneg _ r.2), simp only [zero_le_bit0, zero_le_one]},
  have h_inj : function.injective (coe : {x : ℕ // B ≤ x} → ℕ) := subtype.coe_injective,
  have geom_pos : (0 : ℝ) ≤ c * ∑' (n : {x // B ≤ x}), (2⁻¹ * r⁻¹) ^ n.1,
  { apply mul_nonneg c.2 (tsum_nonneg _),
    intro b,
    rw ← one_div_pow,
    apply pow_nonneg (two_r_nonneg) },
  nth_rewrite 1 [real.norm_eq_abs],
  rw [abs_eq_self.mpr geom_pos],
    apply (norm_tsum_le_tsum_norm _).trans,
  rw [← tsum_mul_left],
  apply tsum_le_tsum,
  { intro b,
    rw [norm_mul, mul_pow, ← one_div_mul_one_div, mul_comm ((1 : ℝ) / 2 ^ b.1) _, ← mul_assoc],
    rw [norm_pow, norm_div, norm_one, real.norm_two, div_pow, one_pow],
    apply (mul_le_mul_right _).mpr,
    apply mem_filtration_le_monomial p c F,
    simp only [one_div, inv_pos, pow_pos, zero_lt_bit0, zero_lt_one] },
  swap,
  { by_cases hc : (c : ℝ) ≠ 0,
    { rw [← summable_mul_left_iff hc],
      simp_rw [← one_div_pow],
      have two_r_lt : (2⁻¹ * r⁻¹ : ℝ) < 1,
      { have := (div_lt_one (nnreal.coe_lt_coe.mpr (r_pos))).mpr half_lt_r,
        simp only [← inv_eq_one_div] at this ⊢,
        rw [div_eq_mul_inv, nnreal.coe_inv, ← mul_inv₀] at this,
        convert this,
        assumption' },
      exact (summable_geometric_of_lt_1 two_r_nonneg two_r_lt).comp_injective h_inj,
      },
    { rw not_ne_iff at hc,
      simp_rw [hc, zero_mul],
      exact summable_zero }, },
  all_goals { simp_rw [norm_mul, norm_pow, norm_div, norm_one, real.norm_two, subtype.val_eq_coe],
    refine ((aux_thm69.summable_iff_on_nat_less F.1.d _).mp (aux_thm69.summable_smaller_radius_norm
      F.1.d (half_lt_r) (F.1.summable punit.star)
      (λ n, lt_d_eq_zero F.1 punit.star n))).comp_injective h_inj,
    intros n hn,
    rw [lt_d_eq_zero F.1 punit.star n hn, norm_zero, zero_mul] },
end


def geom_B_nat (ε : ℝ) (hε : 0 < ε) : {B : ℕ // ∀ (F : filtration (ℒ ϖ) c), ∥ tsum (λ b :
  {n : ℕ // B ≤ n }, ((F.1 punit.star b.1) : ℝ) * (2⁻¹) ^ b.1 ) ∥ < ε ^ (p⁻¹ : ℝ)} :=
begin
  let g := (λ n : ℕ, (c : ℝ) * ((2⁻¹ * r⁻¹) ^ n)),
  have := tendsto_tsum_compl_at_top_zero g,
  rw tendsto_at_top at this,
  have h_pos : 0 < ε ^ (p⁻¹ : ℝ) := real.rpow_pos_of_pos hε _,
  specialize this (ε ^ (p⁻¹ : ℝ)) h_pos,
  let A := this.some,
    let B₀ : option ℕ → ℕ := λ a : (option ℕ), option.rec_on a (0 : ℕ) (λ n, n),
    set B := (B₀ A.max).succ with hB,
    use B,
    have h_incl : A ≤ finset.range B,
    rw finset.le_eq_subset,
    { by_cases H : A.nonempty,
      { intros a ha,
        obtain ⟨s, hs⟩ := finset.max_of_nonempty H,
        replace hB : s.succ = B := by {simp only [*, option.mem_def] at *},
        have h_mem := finset.mem_range_succ_iff.mpr (finset.le_max_of_mem ha hs),
        rwa hB at h_mem },
      { intros a ha,
        rw [finset.not_nonempty_iff_eq_empty] at H,
        finish }},
    let hA := this.some_spec,
    specialize hA (finset.range B) h_incl,
    rw [real.dist_0_eq_abs, ← real.norm_eq_abs] at hA,
    intro F,
    apply lt_of_le_of_lt (mem_filtration_sum_le_geom p c F B),
    convert hA using 1,
    apply congr_arg,
    simp_rw [subtype.val_eq_coe, ← tsum_mul_left],
    have set_eq : {n : ℕ | B ≤ n} = {n : ℕ | n ∉ finset.range B} :=
      by {simp only [finset.mem_range, not_lt]},
    exact tsum_congr_subtype g set_eq,
end


def eq_le_int_nat (B : ℕ) : {n : ℤ // (B : ℤ) ≤ n } ≃ {n : ℕ // B ≤ n} :=
{ to_fun :=
  begin
    intro b,
    use (int.eq_coe_of_zero_le ((int.coe_nat_nonneg B).trans b.2)).some,
    rw ← int.coe_nat_le,
    convert b.2,
    exact (Exists.some_spec (int.eq_coe_of_zero_le ((int.coe_nat_nonneg B).trans b.2))).symm,
  end,
  inv_fun := λ n, ⟨n, by {simp only [coe_coe, int.coe_nat_le], from n.2}⟩,
  left_inv :=
  begin
    rintro ⟨_, h⟩,
    simp only [coe_coe, subtype.coe_mk],
    exact (Exists.some_spec (int.eq_coe_of_zero_le ((int.coe_nat_nonneg B).trans h))).symm,
  end,
  right_inv :=
  begin
    rintro ⟨_, h⟩,
    simp only [coe_coe, subtype.coe_mk, int.coe_nat_inj'],
    exact ((@exists_eq' _ _).some_spec).symm,
  end, }


def geom_B_int (ε : ℝ) (hε : 0 < ε) : {B : ℤ // ∀ (F : filtration (ℒ ϖ) c), ∥ tsum (λ b :
  {n : ℤ // B ≤ n }, ((F.1 punit.star b.1) : ℝ) * (2⁻¹) ^ b.1 ) ∥ < ε ^ (p⁻¹ : ℝ)} :=
begin
  let ℬ := geom_B_nat p c ε hε,
  let B := ℬ.1,
  let hB := ℬ.2,
  use B,
  intro F,
  specialize hB F,
  convert hB using 1,
  apply congr_arg,
  exact ((eq_le_int_nat B).symm.tsum_eq (λ b : {n : ℤ // ↑B ≤ n },
  ((F.1 punit.star b.1) : ℝ) * (2⁻¹) ^ b.1 )).symm,
end


def geom_B (ε : ℝ) (hε : 0 < ε) : ℤ := (geom_B_int c ε hε).1


lemma tail_B (ε : ℝ) (hε : 0 < ε) :  ∀ (F : filtration (ℒ ϖ) c), ∥ tsum (λ b : {n : ℤ // geom_B c ε hε ≤ n },
  ((F.1 punit.star b.1) : ℝ) * (2⁻¹) ^ b.1 ) ∥ < ε ^ (p⁻¹ : ℝ) :=
begin
  intro F,
  have := (geom_B_int p c ε hε).2 F,
  exact this,
end


def U (F : filtration (ℒ ϖ) c) (B : ℤ) : set (filtration (ℒ ϖ) c) := λ G, ∀ s n, n < B → F s n = G s n


lemma mem_U (F : filtration (ℒ ϖ) c) (B : ℤ) : F ∈ (U c F B) := λ _ _ _, rfl


lemma is_open_U (F : filtration (ℒ ϖ) c) (B : ℤ) : is_open (U c F B) :=
begin
  sorry,
end

end topological_generalities


def θ_c (c : ℝ≥0) (T : Fintype) : (filtration (laurent_measures r T) c) →
  (filtration (real_measures p T) c) :=
begin
  intro f,
  rw [← one_mul c],
  use ⟨θ f, θ_bound p c f f.2⟩,
end

lemma commute_seval_ℒ_ℳ (c : ℝ≥0) (s : S) :
  (θ_c c (Fintype.of punit)) ∘ (seval_ℒ_c c s) = (seval_ℳ_c S c s) ∘ (θ_c c S) := by simpa only
  [seval_ℳ_c, seval_ℒ_c, seval_ℒ, θ_c, one_mul, subtype.coe_mk, eq_mpr_eq_cast, set_coe_cast]


lemma continuous_of_seval_ℳ_comp_continuous (c : ℝ≥0) {X : Type*} [topological_space X]
  {f : X → (filtration (ℳ S) c)} : (∀ s, continuous ((seval_ℳ_c S c s) ∘ f)) → continuous f :=
begin
  intro H,
  replace H : ∀ (s : S), continuous (λ x : X, ((homeo_box_ϖ p S c) ∘ (α p S c)) (f x) s),
  { intro,
    rw [seval_ℳ_α_commute' p S c s],
    exact H s },
  rw ← continuous_pi_iff at H,
  convert_to (continuous (λ x, (homeo_box_ϖ p S c) (α p S c (f x)))) using 0,
  { apply eq_iff_iff.mpr,
    rw [homeomorph.comp_continuous_iff, (inducing_α p S c).continuous_iff] },
  exact H,
end


lemma tsum_subtype_sub {f g : ℤ → ℝ} {B : ℤ}
  (hf : summable (λ (b : {x // B ≤ x}), f b * (2⁻¹) ^ b.1))
  (hg : summable (λ (b : {x // B ≤ x}), g b * (2⁻¹) ^ b.1)) :
  ∥ tsum ((λ (b : ℤ), (((g b) : ℝ) - f b) * (2⁻¹) ^ b) ∘ (coe : {b | B ≤ b} → ℤ)) ∥ =
  ∥ ∑' (b : {x // B ≤ x}), (g b : ℝ) * (2⁻¹) ^ b.1 - ∑' (b : {x // B ≤ x}),
    (f b : ℝ) * (2⁻¹) ^ b.1 ∥ :=
begin
  rw [← tsum_sub hg hf, tsum_eq_tsum_of_has_sum_iff_has_sum],
  intro _,
  simp_rw [sub_mul, iff_eq_eq],
  refl,
end

lemma aux_summability_no_norm (F : filtration (ℒ ϖ) c) : summable
  (λ b : ℤ, (((F punit.star b) : ℝ) * (2⁻¹) ^ b)) := aux_thm69.summable_smaller_radius F.1.d (F.1.summable punit.star)
      (λ n, lt_d_eq_zero F.1 punit.star n) half_lt_r

lemma aux_summability_subtype (F : filtration (ℒ ϖ) c) (B : ℤ) : summable (λ b : {x : ℤ // B ≤ x},
  (((F punit.star b) : ℝ) * (2⁻¹) ^ b.1)) :=
    by {exact (aux_summability_no_norm p c F).comp_injective subtype.coe_injective}



lemma pos_ε_pow (ε : ℝ) (hε : 0 < ε) : 0 < (ε / (2 : ℝ) ^ p.1) := by {apply div_pos hε
  (real.rpow_pos_of_pos _ _), simp only [zero_lt_bit0, zero_lt_one]}

lemma dist_lt_of_mem_U (ε : ℝ≥0) (hε : 0 < ε) (F G : filtration (ℒ ϖ) c) :
  G ∈ (U c F (geom_B c (ε / (2 : ℝ) ^ p.1) (pos_ε_pow ε hε))) → ∥ ((θ_c c ϖ G) : (ℳ ϖ)) - (θ_c c ϖ) F ∥ < ε :=
begin
  intro h_mem_G,
  rw real_measures.norm_def,
  simp only [fintype.univ_punit, real_measures.sub_apply, finset.sum_singleton],
  rw [← real.rpow_lt_rpow_iff _ _ _, ← real.rpow_mul,
    mul_inv_cancel, real.rpow_one],
  rotate,
  { rw ← nnreal.coe_zero,
    exact ne_of_gt (nnreal.coe_lt_coe.mpr (fact.out _)) },
  { apply norm_nonneg },
  { apply real.rpow_nonneg_of_nonneg (norm_nonneg _) },
  { rw ← nnreal.coe_zero,
    exact ε.2 },
  { rw [inv_pos, ← nnreal.coe_zero],
    exact (nnreal.coe_lt_coe.mpr (fact.out _)) },
  simp only [θ_c, one_mul, eq_mpr_eq_cast, set_coe_cast, subtype.coe_mk],
  dsimp only [θ, ϑ],
  have h_B : ∀ b : ℤ, b < (geom_B p c (ε / 2 ^ p.1) (pos_ε_pow p ε hε)) → ((G punit.star b) : ℝ) - (F punit.star b) = 0,
  { intros b hb,
    simp only [h_mem_G punit.star b hb, sub_self] },
  rw [← tsum_sub],
  rotate,
  {exact (aux_summability_no_norm p c G)},
  {exact (aux_summability_no_norm p c F)},
  simp_rw [← sub_mul],
  set B := (geom_B p c (ε / 2 ^ p.1) (pos_ε_pow p ε hε)) with def_B,
  let f := λ b : ℤ, ((((G : (ℒ ϖ)) punit.star b) - ((F : (ℒ ϖ)) punit.star b)) : ℝ)
    * (2⁻¹) ^ b,
  let g : ({ b : ℤ | B ≤ b}) → ℝ := f ∘ coe,
  let i : function.support g → ℤ := (coe : { b : ℤ | B ≤ b} → ℤ) ∘ (coe : function.support g → { b : ℤ | B ≤ b}),
  have hi : ∀ ⦃x y : ↥(function.support g)⦄, i x = i y → ↑x = ↑y,
  {intros _ _ h,
    simp only [subtype.coe_inj] at h,
    rwa [subtype.coe_inj] },
  have hf : function.support f ⊆ set.range i,
  { intros a ha,
    simp only [f, function.mem_support, ne.def] at ha,
    have ha' : B ≤ a,
    { by_contra',
      specialize h_B a this,
      simp only [one_div, inv_zpow', zpow_neg₀, mul_eq_zero, inv_eq_zero, not_or_distrib] at ha,
      replace ha := ha.1,
      simpa only },
    simp only [set.mem_set_of_eq, function.mem_support, ne.def, set.mem_range, set_coe.exists],
    use [a, ha', ha, refl _] },
  have hF := tail_B p c (ε.2⁻¹ ^ p.1) (pos_ε_pow p ε hε) F,
  have hG := tail_B p c (ε.2⁻¹ ^ p.1) (pos_ε_pow p ε hε) G,
  rw [real.div_rpow ε.2 _, ← real.rpow_mul] at hF hG,
  simp_rw [@subtype.val_eq_coe _ _ p] at hF hG,
  rw [mul_inv_cancel, real.rpow_one] at hF hG,
  rw [tsum_eq_tsum_of_ne_zero_bij i hi hf (λ _, refl _)],
  dsimp [f, g],
  rw [tsum_subtype_sub],
  apply lt_of_le_of_lt (norm_sub_le _ _),
  convert add_lt_add hG hF,
  simp only [nnreal.val_eq_coe, add_halves'],
  repeat {exact nnreal.coe_ne_zero.mpr (ne_of_gt (fact.out _))},
  repeat {apply (real.rpow_nonneg_of_nonneg)},
  repeat {exact (le_of_lt (@two_pos ℝ _ _))},
  exact (aux_summability_subtype p c F B),
  exact (aux_summability_subtype p c G B),
end

lemma coe_pow_half (η : ℝ) (η_pos' : 0 < η) (η₀ : ℝ≥0) (hη₀ : η₀ = ⟨η, le_of_lt η_pos'⟩) :
  (η / 2) ^ (p : ℝ) = ((η₀ ^ (p : ℝ) : ℝ)) / 2 ^ (p.1) := by {rw [real.div_rpow (le_of_lt η_pos') _,
     nnreal.val_eq_coe, hη₀, subtype.coe_mk], simp only [zero_le_bit0, zero_le_one]}

section
variables {c}

def ξ (F : filtration (ℒ ϖ) c) : ℝ :=
(homeo_filtration_ϖ_ball c) (θ_c c (Fintype.of punit) F)

def hξ (F : filtration (ℒ ϖ) c) :
  ξ F = (homeo_filtration_ϖ_ball c) (θ_c c (Fintype.of punit) F) := rfl

lemma speed_aux' (ε η : ℝ) (η₀ : ℝ≥0) (hη₀ : η = η₀)
  (y : (closed_ball (0 : ℝ) (c ^ (p : ℝ)⁻¹)))
  (F G : (filtration (ℒ (Fintype.of punit)) c))
  (hF : |(((homeo_filtration_ϖ_ball c) (θ_c c (Fintype.of punit) F)) : ℝ) - y| < ε)
  (hη : η = ε - |(homeo_filtration_ϖ_ball c (θ_c c ϖ F)) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ))
  (h_pos : 0 < (η / 2) ^ (p:ℝ))
  (hp : 0 < (p:ℝ))
  (η_pos' : 0 < η)
  (h_η_η₀ : (η / 2) ^ (p:ℝ) = ↑η₀ ^ (p:ℝ) / 2 ^ p.val) (h_pos'')
  (hG : G ∈ U c F (geom_B c ((↑η₀ ^ (p:ℝ) / 2 ^ p.val)) h_pos'')) :
  ∥(θ_c c (Fintype.of punit) G).val - (θ_c c (Fintype.of punit) F).val∥ < η ^ (p:ℝ) :=
begin
  have foo : 0 < η₀ ^ (p:ℝ),
  { apply real.rpow_pos_of_pos, rw ← hη₀, exact η_pos' },
  -- exact dist_lt_of_mem_U p c (η₀ ^ (p : ℝ)) (real.rpow_pos_of_pos η_pos' _) F G hG
  have := dist_lt_of_mem_U p c (η₀ ^ (p : ℝ)) foo F G hG,
  convert this,
end

lemma speed_aux (ε η : ℝ) (η₀ : ℝ≥0) (hη₀ : η = η₀)
  (y : (closed_ball (0 : ℝ) (c ^ (p : ℝ)⁻¹)))
  (F G : (filtration (ℒ (Fintype.of punit)) c))
  (hF : |(((homeo_filtration_ϖ_ball c) (θ_c c (Fintype.of punit) F)) : ℝ) - y| < ε)
  (hη : η = ε - |(homeo_filtration_ϖ_ball c (θ_c c ϖ F)) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ))
  (h_pos : 0 < (η / 2) ^ (p:ℝ))
  (hp : 0 < (p:ℝ))
  (η_pos' : 0 < η)
  (h_η_η₀ : (η / 2) ^ (p:ℝ) = ↑η₀ ^ (p:ℝ) / 2 ^ p.val) (h_pos'')
  (hG : G ∈ U c F (geom_B c ((↑η₀ ^ (p:ℝ) / 2 ^ p.val)) h_pos'')) :
  |ξ G - ξ F| < ε - |ξ F - y| :=
begin
  repeat {rw hξ},
  rw [← real_measures.dist_eq,
    ← real.rpow_lt_rpow_iff
      (real.rpow_nonneg_of_nonneg (real_measures.norm_nonneg _) _) (sub_nonneg.mpr (le_of_lt hF)) hp,
    ← real.rpow_mul (real_measures.norm_nonneg _),
    inv_mul_cancel (ne_of_gt hp), real.rpow_one, ← hη],
  apply speed_aux', assumption'
end

lemma speed (ε η : ℝ) (y : closed_ball (0 : ℝ) (c ^ (p⁻¹ : ℝ)))
  (F G : filtration (ℒ ϖ) c)
  (hF : |(((homeo_filtration_ϖ_ball c) (θ_c c (Fintype.of punit) F)) : ℝ) - y| < ε)
  (hη : η = ε - |(homeo_filtration_ϖ_ball c (θ_c c ϖ F)) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ))
  (hG : G ∈ U c F (geom_B c ((η / 2) ^ (p:ℝ)) h_pos)) :
  |(ξ G) - (ξ F)| + |(ξ F) - y| < ε - |(ξ F) - y| + |(ξ F) - y| :=
begin
  have hp : 0 < (p : ℝ), { rw [← nnreal.coe_zero, nnreal.coe_lt_coe], from fact.out _ },
  have η_pos' : 0 < η := by {rw hη, from (sub_pos.mpr hF)},
  set η₀ : ℝ≥0 := ⟨η, le_of_lt η_pos'⟩ with hη₀,
  have h_η_η₀ := @coe_pow_half p _ _ η η_pos' η₀ hη₀,
  simp_rw [h_η_η₀] at hG,
  apply add_lt_add_right,
  apply @speed_aux p _ _ c ε η η₀ _ y F G,
  assumption',
  rw hη₀, refl,
end

end

lemma U_subset_preimage' (ε η : ℝ) (y : closed_ball (0 : ℝ) (c ^ (p⁻¹ : ℝ)))
  (F : filtration (ℒ ϖ) c)
  (hF : |(((homeo_filtration_ϖ_ball c) (θ_c c (Fintype.of punit) F)) : ℝ) - y| < ε)
  (hη : η = ε - |(homeo_filtration_ϖ_ball c (θ_c c ϖ F)) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ))
  (G : (filtration (ℒ (Fintype.of punit)) c))
  (hG : G ∈ U c F (geom_B c ((η / 2) ^ (p:ℝ)) h_pos)) :
  |ξ G - y| < ε :=
begin
  have aux : |(ξ p G) - (ξ p F)| + |(ξ p F) - y | < ε - | (ξ p F) - y | + | (ξ p F) - y |,
  { apply speed; assumption },
  replace aux : |(ξ p G) - (ξ p F)| + |(ξ p F) - y | < ε,
  { rwa [sub_add_cancel ε (| (ξ p F) - y |)] at aux },
  have := lt_of_le_of_lt (abs_sub_le (ξ p G) (ξ p F) y) aux,
  rw ← real.norm_eq_abs at this ⊢,
  exact this,
end

lemma U_subset_preimage (ε η : ℝ) (y : closed_ball (0 : ℝ) (c ^ (p⁻¹ : ℝ)))
  (F : filtration (ℒ ϖ) c)
  (hF : |(((homeo_filtration_ϖ_ball c) (θ_c c (Fintype.of punit) F)) : ℝ) - y| < ε)
  (hη : η = ε - |(homeo_filtration_ϖ_ball c (θ_c c ϖ F)) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ)) :
  (U c F (geom_B c ((η / 2) ^ (p : ℝ)) h_pos) )  ⊆
    ((homeo_filtration_ϖ_ball c) ∘ θ_c c (ϖ) ⁻¹' (ball y ε)) :=
begin
  intros G hG,
  simp only [set.mem_preimage, one_mul, eq_self_iff_true, eq_mpr_eq_cast, set_coe_cast,
    function.comp_app, mem_ball, subtype.dist_eq, real.dist_eq],
  apply U_subset_preimage'; assumption,
end


-- This is the main continuity property needed in `ses2.lean`
theorem continuous_θ_c (c : ℝ≥0) : continuous (θ_c c S) :=
begin
  apply continuous_of_seval_ℳ_comp_continuous,
  intro s,
  rw ← commute_seval_ℒ_ℳ,
  refine continuous.comp _ (continuous_seval_ℒ_c p S c s),
  apply (homeo_filtration_ϖ_ball c).comp_continuous_iff.mp,
  apply reduction_balls,
  intros y ε,
  rw is_open_iff_forall_mem_open,
  intros F hF,
  simp only [set.mem_preimage, one_mul, eq_self_iff_true, eq_mpr_eq_cast, set_coe_cast,
    function.comp_app, mem_ball, subtype.dist_eq, real.dist_eq] at hF,
  set η := ε - |(homeo_filtration_ϖ_ball c (θ_c p c ϖ F)) - y| with hη,
  have η_pos' : 0 < η := by {rw hη, from (sub_pos.mpr hF)},
  have η_pos : 0 < (η / 2) ^ (p : ℝ) := real.rpow_pos_of_pos (half_pos η_pos') _,
  set V := U p c F (geom_B p c ((η / 2) ^ (p : ℝ)) η_pos) with hV,
  simp_rw [real.div_rpow (le_of_lt η_pos') (le_of_lt (@two_pos ℝ _ _))] at hV,
  use V,
  exact and.intro (U_subset_preimage p c ε η y F hF hη η_pos)
    (and.intro (is_open_U p c F _) (mem_U p c F _)),
end


end theta

end laurent_measures_ses
