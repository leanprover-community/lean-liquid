import analysis.special_functions.pow
import analysis.special_functions.log
import analysis.specific_limits.basic
import category_theory.Fintype
import analysis.normed_space.basic

import pseudo_normed_group.basic
import pseudo_normed_group.category

import laurent_measures.basic

import for_mathlib.tsum
import for_mathlib.nnreal

universe u

noncomputable theory
open_locale big_operators nnreal classical

-- PR #13130
lemma int.abs_le_floor_nnreal_iff (z : ℤ) (c : ℝ≥0) : |z| ≤ ⌊c⌋₊ ↔ ∥z∥₊ ≤ c :=
begin
  rw [int.abs_eq_nat_abs, int.coe_nat_le, nat.le_floor_iff (zero_le c)],
  congr',
  exact nnreal.coe_nat_abs z,
end

/-- `invpoly r S`, with notation `ℤ[T⁻¹] S`, is the functions `S → ℤ[T⁻¹]`. -/
@[derive add_comm_group]
def invpoly (r : ℝ≥0) (S : Fintype) := S → polynomial ℤ

variables {r : ℝ≥0} {S S' : Fintype.{u}}

local notation `ℤ[T⁻¹]` := invpoly r

namespace invpoly

@[simp] lemma add_apply (F G : ℤ[T⁻¹] S) (s : S) : (F + G) s = F s + G s := rfl
@[simp] lemma sub_apply (F G : ℤ[T⁻¹] S) (s : S) : (F - G) s = F s - G s := rfl
@[simp] lemma neg_apply (F : ℤ[T⁻¹] S) (s : S) : (-F) s = -(F s) := rfl
@[simp] lemma zero_apply (s : S) : (0 : ℤ[T⁻¹] S) s = 0 := rfl
@[simp] lemma nsmul_apply (k : ℕ) (F : ℤ[T⁻¹] S) (s : S) : (k • F) s = k • (F s) := rfl
@[simp] lemma zsmul_apply (k : ℤ) (F : ℤ[T⁻¹] S) (s : S) : (k • F) s = k • (F s) := rfl

-- @[ext]
-- lemma ext (F G : ℤ[T⁻¹] S) : (F : S → ) = G → F = G :=
-- by { intros h, funext s, ext, exact congr_fun (congr_fun h s) n }

protected lemma nnreal_summable (F : ℤ[T⁻¹] S) (s : S) :
  summable (λ n, ∥(F s).coeff n∥₊ * r ^ (-n:ℤ)) :=
begin
  apply @summable_of_ne_finset_zero _ _ _ _ _ (F s).support,
  intros n hn,
  simp only [polynomial.mem_support_iff, not_not] at hn,
  simp only [hn, nnnorm_zero, zero_mul],
end

protected lemma summable (F : ℤ[T⁻¹] S) (s : S) :
  summable (λ n, ∥(F s).coeff n∥ * r ^ (-n : ℤ)) :=
begin
  simpa only [← nnreal.summable_coe, nnreal.coe_mul, coe_nnnorm, nnreal.coe_zpow]
    using F.nnreal_summable s
end

-- Move me
lemma nonneg_of_norm_mul_zpow (k n : ℤ) (r : ℝ≥0) : 0 ≤ ∥ k ∥ * (r : ℝ)^n :=
mul_nonneg (norm_nonneg _) (zpow_nonneg (nnreal.coe_nonneg _) _)

def map (f : S ⟶ S') : ℤ[T⁻¹] S → ℤ[T⁻¹] S' := λ F,
λ s', ∑ s in finset.univ.filter (λ t, f t = s'), F s

@[simp] lemma map_apply (f : S ⟶ S') (F : ℤ[T⁻¹] S) (s' : S') (k : ℕ) :
  (map f F s').coeff k = ∑ s in finset.univ.filter (λ t, f t = s'), (F s).coeff k :=
by simp only [map, ← polynomial.finset_sum_coeff]

@[simp] lemma map_id : (map (𝟙 S) : ℤ[T⁻¹] S → ℤ[T⁻¹] S) = id :=
begin
  ext F s k,
  simp only [map_apply, Fintype.id_apply, id.def, finset.sum_filter,
    finset.sum_ite_eq', finset.mem_univ, if_true],
end

@[simp] lemma map_comp {S'' : Fintype.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
  (map (f ≫ g) : ℤ[T⁻¹] S → ℤ[T⁻¹] S'') = map g ∘ map f :=
begin
  ext F s k,
  simp only [function.comp_app, map_apply, finset.sum_congr],
  rw ← finset.sum_bUnion,
  { apply finset.sum_congr,
    { change finset.univ.filter (λ t, g (f t) = s) = _,
      ext i,
      split;
      { intro hi, simpa only [finset.mem_bUnion, finset.mem_filter, finset.mem_univ, true_and,
          exists_prop, exists_eq_right'] using hi } },
    { intros, refl } },
  { intros i hi j hj h k hk,
    simp only [finset.inf_eq_inter, finset.mem_inter, finset.mem_filter, finset.mem_univ, true_and,
      finset.coe_filter, finset.coe_univ, set.sep_univ, set.mem_set_of_eq] at hi hj hk,
    refine h _,
    rw [← hk.1, ← hk.2] }
end

instance : has_norm (ℤ[T⁻¹] S) :=
⟨λ F, ∑ s, ∑' n, ∥(F s).coeff n∥ * (r : ℝ) ^ (-n:ℤ)⟩

lemma norm_def (F : ℤ[T⁻¹] S) : ∥F∥ = ∑ s, ∑' n, ∥(F s).coeff n∥ * (r : ℝ)^(-n:ℤ) := rfl

instance : has_nnnorm (ℤ[T⁻¹] S) :=
⟨λ F, ∑ s, ∑' n, ∥(F s).coeff n∥₊ * r ^ (-n : ℤ)⟩

lemma nnnorm_def (F : ℤ[T⁻¹] S) : ∥F∥₊ = ∑ s, ∑' n, ∥(F s).coeff n∥₊ * r^(-n:ℤ) := rfl

@[simp] lemma coe_nnnorm (F : ℤ[T⁻¹] S) : (∥F∥₊ : ℝ) = ∥F∥ :=
by simp only [nnnorm_def, norm_def, nnreal.coe_sum, nnreal.coe_tsum,
  nonneg.coe_mul, coe_nnnorm, nnreal.coe_zpow]

@[simp] lemma invpoly.norm_nonneg (F : ℤ[T⁻¹] S) : 0 ≤ ∥F∥ :=
by rw [← coe_nnnorm]; exact ∥F∥₊.coe_nonneg

@[simp] lemma nnnorm_neg (F : ℤ[T⁻¹] S) : ∥-F∥₊ = ∥F∥₊ :=
by simp only [nnnorm_def, nnnorm_neg, neg_apply, polynomial.coeff_neg]

lemma nnnorm_add (F G : ℤ[T⁻¹] S) : ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  simp only [nnnorm_def, ← finset.sum_add_distrib],
  apply finset.sum_le_sum,
  rintro s -,
  rw ← tsum_add (F.nnreal_summable _) (G.nnreal_summable _),
  refine tsum_le_tsum _ ((F + G).nnreal_summable _)
    ((F.nnreal_summable s).add (G.nnreal_summable s)),
  intro b,
  simp [← add_mul],
  refine mul_le_mul' (nnnorm_add_le _ _) le_rfl
end

lemma norm_add (F G : ℤ[T⁻¹] S) : ∥F + G∥ ≤ ∥F∥ + ∥G∥ :=
by simpa only [← coe_nnnorm, ← nnreal.coe_add, nnreal.coe_le_coe] using nnnorm_add F G


instance : pseudo_normed_group (ℤ[T⁻¹] S) :=
{ filtration := λ c, { F | ∥F∥₊ ≤ c },
  filtration_mono := λ c₁ c₂ h F hF, by {dsimp at *, exact le_trans hF h},
  zero_mem_filtration := λ c, by simp [nnnorm_def],
  neg_mem_filtration := λ c F h, (nnnorm_neg F).le.trans h,
  add_mem_filtration := λ c₁ c₂ F₁ F₂ h₁ h₂, (nnnorm_add _ _).trans (add_le_add h₁ h₂) }

@[simp] lemma mem_filtration_iff (F : ℤ[T⁻¹] S) (c : ℝ≥0) :
  F ∈ pseudo_normed_group.filtration (ℤ[T⁻¹] S) c ↔ ∥F∥₊ ≤ c := iff.rfl

section
open finset

lemma map_bound (f : S ⟶ S') (F : ℤ[T⁻¹] S) : ∥map f F∥₊ ≤ ∥F∥₊ := calc
∥map f F∥₊ = ∑ s', ∑' n, ∥∑ s in univ.filter (λ t, f t = s'), (F s).coeff n∥₊ * (r^(-n:ℤ)) :
  (by simp only [map, ← polynomial.finset_sum_coeff]; refl)
... ≤ ∑ s', ∑' n, ∑ s in univ.filter (λ t, f t = s'), ∥(F s).coeff n∥₊ * r^(-n:ℤ) : begin
  apply sum_le_sum,
  rintros s' -,
  have h1 : summable (λ n : ℕ, ∑ (s : S.α) in univ.filter (λ t, f t = s'), ∥(F s).coeff n∥₊ * r^(-n:ℤ)) :=
    summable_sum (λ s _, F.nnreal_summable s),
  have h2 : ∀ b : ℕ,
    ∥∑ (s : S.α) in univ.filter (λ t, f t = s'), (F s).coeff b∥₊ * r ^ (-b:ℤ) ≤
      ∑ (s : S.α) in univ.filter (λ t, f t = s'), ∥(F s).coeff b∥₊ * r ^ (-b:ℤ),
  { intros b, rw ← sum_mul, exact mul_le_mul' (nnnorm_sum_le _ _) le_rfl },
  apply tsum_le_tsum h2 (nnreal.summable_of_le h2 h1) h1,
end
... = ∑ s', ∑ s in univ.filter (λ t, f t = s'), ∑' n, ∥(F s).coeff n∥₊ * r^(-n:ℤ) :
  sum_congr rfl (λ s' _, tsum_sum $ λ s _, F.nnreal_summable _)
... = _ : begin
  rw [← sum_bUnion],
  refine sum_congr _ _,
  { ext s, simp only [mem_bUnion, mem_univ, mem_filter, true_and, exists_true_left, exists_eq'] },
  { intros, refl },
  { rintro x - y - h i hi,
    apply h,
    simp only [inf_eq_inter, mem_inter, mem_filter, mem_univ, true_and] at hi,
    rw [← hi.1, ← hi.2] }
end

end

lemma map_bound' (f : S ⟶ S') (F : ℤ[T⁻¹] S) : ∥map f F∥ ≤ ∥F∥ :=
by simpa only [← coe_nnnorm, ← nnreal.coe_add, nnreal.coe_le_coe] using map_bound f F

lemma bounded_of_filtration (F : ℤ[T⁻¹] S) (c : ℝ≥0) [hr : fact (0 < r)] :
  ∥F∥₊ ≤ c → ∀ (s : S) (n : ℕ), ∥(F s).coeff n∥₊ ≤ c * r^n :=
begin
  intros hF s n,
  have : ∥(F s).coeff n∥₊ * r ^ (-n : ℤ) ≤ ∑' k, ∥(F s).coeff k∥₊ * r ^ (-k:ℤ),
  { exact le_tsum (F.nnreal_summable s) _ (λ k _, zero_le'), },
  rw [mul_comm, nnreal.mul_le_iff_le_inv (zpow_ne_zero_of_ne_zero (hr.elim.ne).symm _)] at this,
  simp only [zpow_neg₀, zpow_coe_nat, inv_inv, mul_comm (r^n)] at this,
  refine le_trans this _,
  rw mul_le_mul_right (pow_pos hr.elim n),
  refine le_trans _ hF,
  unfold nnnorm,
  simp only [zpow_neg₀, zpow_coe_nat],
  apply @finset.single_le_sum S ℝ≥0 _ (λ s, ∑' n, ∥(F s).coeff n∥₊ * (r^n)⁻¹),
    { rintros s -, exact zero_le', },
    { exact finset.mem_univ _ }
end

lemma bounded_of_filtration' (F : ℤ[T⁻¹] S) (c : ℝ≥0) [fact (0 < r)] [hr : fact (r < 1)] :
  ∥F∥₊ ≤ c → ∀ (s : S) (n : ℕ), |(F s).coeff n| ≤ ⌊c⌋₊ :=
begin
  intros hF s n,
  rw int.abs_le_floor_nnreal_iff,
  refine le_trans (bounded_of_filtration F c hF s n) _,
  exact mul_le_of_le_of_le_one (le_refl c) (pow_le_one' hr.elim.le n),
end

-- rather annoyingly, can't use `bounded_of_filtration` to prove this
-- more easily because it's true even if r=0 :-)
/-- This lemma puts bounds on where `(F s).coeff n` can be nonzero. -/
lemma eq_zero_of_filtration (F : ℤ[T⁻¹] S) (c : ℝ≥0) :
  ∥F∥₊ ≤ c → ∀ (s : S) (n : ℕ), c < r^(-n:ℤ) → (F s).coeff n = 0 :=
begin
  intros hF s n h,
  suffices : ∥(F s).coeff n∥₊ < 1,
  { change abs ((F s).coeff n : ℝ) < 1 at this,
    norm_cast at this,
    rwa ← int.eq_zero_iff_abs_lt_one },
  have : ∥(F s).coeff n∥₊ * r ^ (-n : ℤ) ≤ ∑' k, ∥(F s).coeff k∥₊ * r ^ (-k:ℤ),
  { exact le_tsum (F.nnreal_summable s) _ (λ k _, zero_le'), },
  replace this := lt_of_le_of_lt (this.trans _) h,
  { have hr₁ : 0 < r^(-n:ℤ) := lt_of_le_of_lt zero_le' h,
    have hr₂ : r^(-n:ℤ) ≠ 0 := hr₁.ne',
    convert mul_lt_mul this (le_refl (r ^ (-n : ℤ))⁻¹) _ hr₁.le,
    { exact (mul_inv_cancel_right₀ hr₂ _).symm },
    { exact (mul_inv_cancel hr₂).symm },
    { rwa nnreal.inv_pos }, },
  { refine le_trans _ hF,
    apply @finset.single_le_sum S ℝ≥0 _ (λ s, ∑' n, ∥(F s).coeff n∥₊ * r^(-n:ℤ)),
    { rintros s -, exact zero_le', },
    { exact finset.mem_univ _ } }
end

lemma log_div_log_lt {r : ℝ≥0} (c : ℝ≥0) (n : ℕ)
  (hr0 : 0 < r)
  (hr1 : r < 1)
  (h : -real.log ↑c / real.log ↑r < ↑n) :
  c < r ^ -(n : ℤ) :=
begin
  rcases c.eq_zero_or_pos with (rfl | hc),
  { apply nnreal.zpow_pos hr0.ne.symm, },
  { rw [div_lt_iff_of_neg (real.log_neg hr0 hr1), lt_neg, ← neg_mul] at h,
    rw [(by norm_cast :  -(n : ℝ) = (-(n : ℤ) : ℤ)), ← real.log_zpow] at h,
    rw real.log_lt_log_iff hc at h,
    { exact_mod_cast h },
    { norm_cast, apply nnreal.zpow_pos hr0.ne.symm } },
end

lemma eq_zero_of_filtration' (F : ℤ[T⁻¹] S) (c : ℝ≥0) [hr0 : fact (0 < r)] [hr1 : fact (r < 1)] :
  ∥F∥₊ ≤ c → ∀ (s : S) (n : ℕ), -real.log(c)/real.log(r) < n → (F s).coeff n = 0 :=
begin
  intros hF s n h,
  refine eq_zero_of_filtration F c hF s n (log_div_log_lt c n hr0.elim hr1.elim h),
end

-- move me
lemma zpow_strict_anti {K : Type} [linear_ordered_field K] {x : K} (hx₀ : 0 < x) (hx₁ : x < 1) :
  strict_anti (λ n:ℤ, x ^ n) :=
begin
  intros n m H,
  rw [← inv_inv x],
  simp only [inv_zpow₀ x⁻¹, inv_lt_inv (zpow_pos_of_pos (inv_pos.mpr hx₀) _)
    (zpow_pos_of_pos (inv_pos.mpr hx₀) _)],
  exact zpow_strict_mono (one_lt_inv hx₀ hx₁) H,
end

section profinite_structure

variables [fact (0 < r)] (c : ℝ≥0)

instance [fact (r < 1)] : fintype { F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c} := sorry

instance : topological_space { F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c} := ⊥

instance [fact (0 < r)] [fact (r < 1)] : profinitely_filtered_pseudo_normed_group (ℤ[T⁻¹] S) :=
{ continuous_add' := λ _ _, continuous_of_discrete_topology,
  continuous_neg' := λ _, continuous_of_discrete_topology,
  continuous_cast_le := λ _ _ _, continuous_of_discrete_topology,
  ..(infer_instance : (pseudo_normed_group (ℤ[T⁻¹] S))) }
.

end profinite_structure

/--
The `T⁻¹` action on `ℤ[T⁻¹] S`.
This is defined, essentially, as a shift in `ℕ` (accounting for the restriction at 0).
This is an additive group homomorphism.
-/
def Tinv_aux {S : Fintype.{u}} :
  ℤ[T⁻¹] S →+ ℤ[T⁻¹] S :=
add_monoid_hom.mk' (λ F s, add_monoid_hom.mul_left polynomial.X (F s))
  (by { intros F G, funext s, exact map_add _ _ _ })

lemma Tinv_aux_coeff (F : ℤ[T⁻¹] S) (s : S) (n : ℕ) :
  (Tinv_aux F s).coeff n = (polynomial.X * F s).coeff n := rfl

@[simp] lemma Tinv_aux_zero (F : ℤ[T⁻¹] S) (s : S) : (Tinv_aux F s).coeff 0 = 0 :=
by simp only [Tinv_aux_coeff, polynomial.mul_coeff_zero, polynomial.coeff_X_zero, zero_mul]

@[simp] lemma Tinv_aux_succ (F : ℤ[T⁻¹] S) (s : S) (i : ℕ) :
  (Tinv_aux F s).coeff (i + 1) = (F s).coeff i :=
by simp only [Tinv_aux_coeff, polynomial.coeff_X_mul]

lemma Tinv_aux_summable [hr : fact (0 < r)] (F : ℤ[T⁻¹] S) (s : S) :
  summable (λ n, (∥(Tinv_aux F s).coeff n∥₊ * r ^ (-n:ℤ))) :=
begin
  rw ← nnreal.summable_nat_add_iff 1,
  simp only [Tinv_aux_succ, int.coe_nat_succ, neg_add, zpow_add₀ hr.out.ne', ← mul_assoc],
  apply summable.mul_right,
  exact F.nnreal_summable s,
end

@[simps]
def Tinv_hom [hr : fact (0 < r)] [fact (r < 1)] :
  comphaus_filtered_pseudo_normed_group_hom (ℤ[T⁻¹] S) (ℤ[T⁻¹] S) :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_bound Tinv_aux r⁻¹
begin
  abstract Tinv_spec {
  intro c,
  refine ⟨_, continuous_of_discrete_topology⟩,
  intros F hF,
  rw mul_comm,
  refine le_trans _ (mul_le_mul' hF le_rfl),
  simp only [nnnorm_def, finset.sum_mul],
  refine finset.sum_le_sum (λ s _, _),
  transitivity ∑' n, ∥(F s).coeff n∥₊ * r^(-n:ℤ) * r⁻¹,
  { rw ← sum_add_tsum_nat_add' 1,
    swap, { apply Tinv_aux_summable },
    simp only [finset.range_one, zpow_neg₀, zpow_coe_nat, finset.sum_singleton,
      pow_zero, inv_one, mul_one, int.coe_nat_succ, neg_add, zpow_add₀ hr.out.ne',
      zpow_one, mul_assoc, Tinv_aux_zero, nnnorm_zero, Tinv_aux_succ, zero_add], },
  refine le_of_eq _, ext,
  simp only [nonneg.coe_mul, nnreal.coe_tsum, coe_nnnorm, nnreal.coe_zpow, tsum_mul_right], }
end
.

instance [fact (0 < r)] [fact (r < 1)] :
  profinitely_filtered_pseudo_normed_group_with_Tinv r (ℤ[T⁻¹] S) :=
{ Tinv := Tinv_hom,
  Tinv_mem_filtration := λ c F hF,
    comphaus_filtered_pseudo_normed_group_hom.mk_of_bound_bound_by _ _ _ hF,
  .. (_: profinitely_filtered_pseudo_normed_group (ℤ[T⁻¹] S))}

open comphaus_filtered_pseudo_normed_group_with_Tinv

lemma Tinv_coeff [fact (0 < r)] [fact (r < 1)] (F : ℤ[T⁻¹] S) (s : S) (n : ℕ) :
  (Tinv F s).coeff n = (polynomial.X * F s).coeff n := rfl

@[simp] lemma Tinv_zero [fact (0 < r)] [fact (r < 1)] (F : ℤ[T⁻¹] S) (s : S) : (Tinv F s).coeff 0 = 0 :=
Tinv_aux_zero F s

@[simp] lemma Tinv_succ [fact (0 < r)] [fact (r < 1)] (F : ℤ[T⁻¹] S) (s : S) (i : ℕ) :
  (Tinv F s).coeff (i + 1) = (F s).coeff i :=
Tinv_aux_succ F s i

variable {α : Type*}

open pseudo_normed_group profinitely_filtered_pseudo_normed_group
  comphaus_filtered_pseudo_normed_group

@[simps]
def map_hom [fact (0 < r)] [fact (r < 1)] (f : S ⟶ S') :
  comphaus_filtered_pseudo_normed_group_with_Tinv_hom r (ℤ[T⁻¹] S) (ℤ[T⁻¹] S') :=
{ to_fun := map f,
  map_zero' := by { ext s n,
    simp only [map_apply, zero_apply, polynomial.coeff_zero, finset.sum_const_zero], },
  map_add' := λ F G, by { ext s n,
    simp only [map_apply, add_apply, polynomial.coeff_add, finset.sum_add_distrib], },
  map_Tinv' := λ F, by { ext s (_|n),
    { simp only [map_apply, Tinv_zero, finset.sum_const_zero], },
    { simp only [map_apply, Tinv_succ], } },
  strict' := λ c F (hF : ∥F∥₊ ≤ c), (map_bound _ _).trans hF,
  continuous' := λ c, continuous_of_discrete_topology }

end invpoly
