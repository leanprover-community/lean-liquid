import analysis.special_functions.pow
import analysis.specific_limits.basic
import analysis.normed_space.basic
import analysis.mean_inequalities_pow
import category_theory.Fintype

import pseudo_normed_group.basic
import pseudo_normed_group.category

import for_mathlib.nnreal
import for_mathlib.real

universe u

noncomputable theory
open_locale big_operators nnreal classical

@[nolint unused_arguments, derive add_comm_group]
def real_measures (p : ℝ≥0) (S : Fintype) := S → ℝ

variables {p : ℝ≥0} {S S' : Fintype.{u}}

local notation `ℳ` := real_measures
local notation `ϖ` := Fintype.of punit

namespace real_measures

@[simp] lemma zero_apply (s : S) : (0 : ℳ p S) s = 0 := rfl

@[simp] lemma add_apply (F G : ℳ p S) (s : S) : (F + G) s = F s + G s := rfl

@[simp] lemma neg_apply (F : ℳ p S) (s : S) : (-F) s = - (F s) := rfl

@[simp] lemma sub_apply (F G : ℳ p S) (s : S) : (F - G) s = F s - G s := rfl

instance : has_norm (ℳ p S) := ⟨λ F, ∑ s, ∥F s∥ ^ (p:ℝ)⟩

lemma norm_def (F : ℳ p S) : ∥F∥ = ∑ s, ∥F s∥ ^ (p:ℝ) := rfl

instance : has_nnnorm (ℳ p S) := ⟨λ F, ∑ s, ∥F s∥₊ ^ (p:ℝ)⟩

lemma nnnorm_def (F : ℳ p S) : ∥F∥₊ = ∑ s, ∥F s∥₊ ^ (p:ℝ) := rfl

@[simp] protected lemma coe_nnnorm (F : ℳ p S) : (∥F∥₊ : ℝ) = ∥F∥ :=
by simp only [norm_def, nnnorm_def, nnreal.coe_sum, nnreal.coe_rpow, coe_nnnorm]

@[simp] protected lemma nnnorm_zero [hp : fact (0 < p)] : ∥(0 : ℳ p S)∥₊ = 0 :=
begin
  rw [nnnorm_def, finset.sum_eq_zero],
  rintro s -,
  rw [zero_apply, nnnorm_zero, nnreal.zero_rpow],
  exact_mod_cast hp.out.ne',
end

-- move this
lemma nnreal.rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0) (hp_pos : 0 < p) (hp1 : p ≤ 1) :
  (a + b) ^ p ≤ a ^ p + b ^ p :=
begin
  rw [← ennreal.coe_le_coe],
  simpa only [← ennreal.coe_rpow_of_nonneg _ hp_pos.le, ennreal.coe_add]
    using ennreal.rpow_add_le_add_rpow a b hp_pos hp1,
end

-- move this
lemma nnreal.rpow_sum_le_sum_rpow
  {ι : Type*} (s : finset ι) {p : ℝ} (a : ι → ℝ≥0) (hp_pos : 0 < p) (hp1 : p ≤ 1) :
  (∑ i in s, a i) ^ p ≤ ∑ i in s, (a i ^ p) :=
begin
  induction s using finset.induction_on with i s his IH,
  { simp only [nnreal.zero_rpow hp_pos.ne', finset.sum_empty, le_zero_iff], },
  { simp only [his, finset.sum_insert, not_false_iff],
    exact (nnreal.rpow_add_le_add_rpow _ _ hp_pos hp1).trans (add_le_add le_rfl IH), }
end

protected lemma nnnorm_add [h0p : fact (0 < p)] [hp1 : fact (p ≤ 1)]
  (F G : ℳ p S) : ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  dsimp [nnnorm_def],
  rw ← finset.sum_add_distrib,
  apply finset.sum_le_sum,
  intros s hs,
  have h0p' : (0 : ℝ) < p, exact_mod_cast h0p.out,
  have hp1' : (p : ℝ) ≤ 1, exact_mod_cast hp1.out,
  exact (nnreal.rpow_le_rpow (nnnorm_add_le _ _) h0p'.le).trans
    (@nnreal.rpow_add_le_add_rpow p (∥F s∥₊) (∥G s∥₊) h0p' hp1'),
end

--needed? [FAE] Yes!
instance png_real_measures [fact (0 < p)] [fact (p ≤ 1)] : pseudo_normed_group (ℳ p S) :=
{ filtration := λ c, { F | ∥F∥₊ ≤ c },
  filtration_mono := λ c₁ c₂ h F hF, by {dsimp at *, exact le_trans hF h},
  zero_mem_filtration := λ c, by simp only [real_measures.nnnorm_zero, zero_le', set.mem_set_of_eq],
  neg_mem_filtration := λ c F h, by { dsimp [nnnorm_def] at *, simp only [h, nnnorm_neg] },
  add_mem_filtration := λ c₁ c₂ F₁ F₂ h₁ h₂,
    (real_measures.nnnorm_add _ _).trans (add_le_add h₁ h₂) }

lemma mem_filtration_iff [fact (0 < p)] [fact (p ≤ 1)] (F : ℳ p S) (c : ℝ≥0) :
  F ∈ pseudo_normed_group.filtration (ℳ p S) c ↔ ∥F∥₊ ≤ c := iff.rfl

def map (f : S ⟶ S') : ℳ p S → ℳ p S' :=
λ F s', ∑ s in finset.univ.filter (λ t, f t = s'), F s

@[simp]
lemma map_apply (f : S ⟶ S') (F : ℳ p S) (s' : S') :
  map f F s' = ∑ s in finset.univ.filter (λ t, f t = s'), F s := rfl

@[simp]
lemma map_id : (map (𝟙 S) : ℳ p S → ℳ p S) = id :=
begin
  ext F s,
  rw [map_apply, finset.sum_filter, id.def],
  simp only [Fintype.id_apply, finset.sum_ite_eq', finset.mem_univ, if_true],
end

@[simp]
lemma map_comp {S'' : Fintype.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
  (map (f ≫ g) : ℳ p S → ℳ p S'') = map g ∘ map f :=
begin
  ext F s,
  simp only [function.comp_app, map_apply],
  convert finset.sum_bUnion _ using 1, swap 2, { classical, apply_instance },
  { apply finset.sum_congr,
    { change finset.univ.filter (λ t, g (f t) = s) = _,
      ext i,
      simp only [true_and, exists_prop, finset.mem_univ, finset.mem_bUnion,
        exists_eq_right', finset.mem_filter] },
    { intros, refl } },
  { intros i hi j hj h k hk,
    refine h _,
    simp only [true_and, finset.inf_eq_inter, finset.mem_univ,
      finset.mem_filter, finset.mem_inter] at hk,
    rw [← hk.1, ← hk.2] }
end

lemma map_bound [h0p : fact (0 < p)] [hp1 : fact (p ≤ 1)] (f : S ⟶ S') (F : ℳ p S) :
  ∥map f F∥₊ ≤ ∥F∥₊ :=
begin
  calc ∑ s', ∥∑ s in finset.univ.filter (λ t, f t = s'), F s∥₊ ^ (p:ℝ)
      ≤ ∑ s' : S', ∑ s in finset.univ.filter (λ t, f t = s'), ∥F s∥₊ ^ (p:ℝ) : _
  ... = ∑ s, ∥F s∥₊ ^ (p:ℝ) : _,
  { apply finset.sum_le_sum,
    rintros s' -,
    have h0p' : (0 : ℝ) < p, exact_mod_cast h0p.out,
    have hp1' : (p : ℝ) ≤ 1, exact_mod_cast hp1.out,
    exact (nnreal.rpow_le_rpow (nnnorm_sum_le _ _) h0p'.le).trans
      (nnreal.rpow_sum_le_sum_rpow _ _ h0p' hp1'), },
  { rw ← finset.sum_bUnion,
    { refine finset.sum_congr _ _,
      { ext s,
        simp only [true_and, finset.mem_univ, finset.mem_bUnion, iff_true,
          exists_true_left, finset.mem_filter],
        refine ⟨_, rfl⟩, },
      { intros, refl } },
    { rintro x - y - h i hi,
      apply h,
      simp only [true_and, finset.inf_eq_inter, finset.mem_univ,
        finset.mem_filter, finset.mem_inter] at hi,
      rw [← hi.1, ← hi.2] } },
end

def seval_ℳ {r : ℝ≥0} (S : Fintype) (s : S): (real_measures r S) →
  (real_measures r (Fintype.of punit)) := λ F, (λ _, F s)

variables [fact (0 < p)] [fact (p ≤ 1)]

open pseudo_normed_group (filtration)

instance topological_space (c : ℝ≥0) : topological_space (filtration (ℳ p S) c) :=
@subtype.topological_space _ _ Pi.topological_space

instance t2_space (c : ℝ≥0) : t2_space (filtration (ℳ p S) c) :=
@subtype.t2_space _ _ Pi.topological_space _

lemma nnnorm_apply_le_of_nnnorm_le (F : ℳ p S) (s : S) (c : ℝ≥0) (h : ∥F∥₊ ≤ c) :
  ∥F s∥₊ ≤ c ^ (p⁻¹ : ℝ) :=
begin
  calc ∥F s∥₊ = (∥F s∥₊ ^ (p:ℝ)) ^ (p⁻¹ : ℝ) : _
  ... ≤ c ^ (p⁻¹ : ℝ) : _,
  { rw_mod_cast [← nnreal.rpow_mul, mul_inv_cancel, nnreal.rpow_one],
    exact ne_of_gt (‹fact (0 < p)›.out) },
  { apply nnreal.rpow_le_rpow _ (inv_pos.mpr _).le,
    { refine le_trans _ h,
      have aux := finset.sum_pi_single' s (∥F s∥₊ ^ (p:ℝ)) finset.univ,
      simp only [finset.mem_univ, if_true] at aux,
      rw ← aux,
      apply finset.sum_le_sum,
      rintro t -,
      split_ifs, { subst t }, { exact zero_le' } },
    { norm_cast, exact ‹fact (0 < p)›.out } }
end

lemma apply_mem_Icc_of_nnnorm_le (F : ℳ p S) (s : S) (c : ℝ≥0) (h : ∥F∥₊ ≤ c) :
  F s ∈ set.Icc (-c ^ (p⁻¹ : ℝ) : ℝ) (c ^ (p⁻¹ : ℝ) : ℝ) :=
begin
  have := @set.mem_Icc_iff_abs_le ℝ _ 0 (F s) (c ^ (p:ℝ)⁻¹),
  simp only [zero_sub, abs_neg, zero_add, ← real.norm_eq_abs, ← coe_nnnorm, nnnorm_neg] at this,
  rw ← this,
  norm_cast,
  exact nnnorm_apply_le_of_nnnorm_le F s c h
end

-- move me
lemma continuous.sum {ι X A : Type*} [topological_space X]
  [topological_space A] [add_comm_monoid A] [has_continuous_add A]
  (s : finset ι) (f : ι → X → A) (hf : ∀ i ∈ s, continuous (f i)) :
  continuous (∑ i in s, f i) :=
begin
  induction s using finset.induction_on with i s his IH,
  { simp only [finset.sum_empty], exact @continuous_zero X A _ _ _ },
  { simp only [his, finset.sum_insert, not_false_iff],
    refine (hf i $ s.mem_insert_self i).add (IH $ λ i hi, hf i $ finset.mem_insert_of_mem hi), }
end

-- move me
lemma continuous.sum' {ι X A : Type*} [topological_space X]
  [topological_space A] [add_comm_monoid A] [has_continuous_add A]
  (s : finset ι) (f : ι → X → A) (hf : ∀ i ∈ s, continuous (f i)) :
  continuous (λ x, ∑ i in s, f i x) :=
begin
  induction s using finset.induction_on with i s his IH,
  { simp only [finset.sum_empty], exact @continuous_zero X A _ _ _ },
  { simp only [his, finset.sum_insert, not_false_iff],
    refine (hf i $ s.mem_insert_self i).add (IH $ λ i hi, hf i $ finset.mem_insert_of_mem hi), }
end

instance compact_space (c : ℝ≥0) : compact_space (filtration (ℳ p S) c) :=
begin
  constructor,
  rw [← embedding_subtype_coe.to_inducing.is_compact_iff],
  simp only [set.image_univ, subtype.range_coe_subtype, set.set_of_mem_eq],
  let d : ℝ := c ^ (p⁻¹ : ℝ),
  let T : set (S → ℝ) := {x | ∀ s, x s ∈ set.Icc (-d) d},
  have hT : is_compact T := is_compact_pi_infinite (λ s, is_compact_Icc),
  refine compact_of_is_closed_subset hT _ (λ F hF s, apply_mem_Icc_of_nnnorm_le F s c hF),
  refine is_closed_le (continuous.sum' _ _ _) continuous_const,
  rintro s -,
  have h0p : 0 ≤ (p : ℝ), { norm_cast, exact fact.out _ },
  exact (nnreal.continuous_rpow_const h0p).comp (continuous_nnnorm.comp (continuous_apply s)),
end

def equiv_filtration_ϖ_Icc (c : ℝ≥0) : filtration (ℳ p ϖ) c ≃ set.Icc ((- c ^ (p⁻¹ : ℝ)) : ℝ)
  (c ^ (p⁻¹ : ℝ) : ℝ):=
begin
  fconstructor,
  { intro f,
    exact ⟨f.1 punit.star, apply_mem_Icc_of_nnnorm_le _ _ _ f.2⟩ },
  { intro x,
    use (λ _, x),
    have := @real.rpow_le_rpow_iff (|↑x| : ℝ) (c ^ (p⁻¹ : ℝ)) p _ _ _,
    rw [← real.rpow_mul, inv_mul_cancel, real.rpow_one] at this,
    have hx := x.2,
    simpa only [mem_filtration_iff, subtype.val_eq_coe, set.mem_Icc, nnnorm, fintype.univ_punit,
      finset.sum_singleton, ← nnreal.coe_le_coe, nnreal.coe_rpow, subtype.coe_mk, real.norm_eq_abs,
      this, abs_le],
    { rw nnreal.coe_ne_zero,
      exact ne_of_gt (fact.out _) },
    { exact c.2 },
    { exact abs_nonneg x },
    { rw ← nnreal.coe_rpow,
     exact (c ^ (p⁻¹ : ℝ)).2 },
    { rw [← nnreal.coe_zero, nnreal.coe_lt_coe],
      exact fact.out _ } },
    { intro f,
      ext s,
      simp only [subtype.val_eq_coe, subtype.coe_mk],
      apply congr_arg,
      simp only [eq_iff_true_of_subsingleton] },
    { intro x,
      simp only [subtype.coe_eta] },
end

def homeo_filtration_ϖ_Icc (c : ℝ≥0) : filtration (ℳ p ϖ) c ≃ₜ set.Icc ((- c ^ (p⁻¹ : ℝ)) : ℝ)
  ((c ^ (p⁻¹ : ℝ)) : ℝ) := sorry
-- { to_equiv := equiv_filtration_ϖ_Icc c,
--   continuous_to_fun := sorry,
--   continuous_inv_fun := sorry
-- }

instance chpng_real_measures : comphaus_filtered_pseudo_normed_group (ℳ p S) :=
{ continuous_add' := begin
    intros c₁ c₂,
    apply continuous_induced_rng,
    simp only [function.comp, pseudo_normed_group.add'_eq],
    exact (continuous_subtype_val.comp continuous_fst).add
          (continuous_subtype_val.comp continuous_snd),
  end,
  continuous_neg' := begin
    intros c,
    apply continuous_induced_rng,
    simp only [function.comp, pseudo_normed_group.neg'_eq],
    exact continuous_subtype_val.neg,
  end,
  continuous_cast_le := begin
    introsI c₁ c₂ h,
    apply continuous_induced_rng,
    simp only [function.comp, pseudo_normed_group.coe_cast_le],
    exact continuous_subtype_val,
  end,
  ..(infer_instance : (pseudo_normed_group (ℳ p S))) }

variable {α : Type*}

open pseudo_normed_group comphaus_filtered_pseudo_normed_group

@[simps]
def map_hom [fact (0 < p)] (f : S ⟶ S') :
  strict_comphaus_filtered_pseudo_normed_group_hom (ℳ p S) (ℳ p S') :=
{ to_fun := map f,
  map_zero' := by { ext F s i, simp only [map_apply, finset.sum_const_zero, zero_apply], },
  map_add' := λ F G, by { ext s i, simp only [finset.sum_add_distrib, add_apply, map_apply], },
  strict' := λ c F hF, (map_bound _ _).trans hF,
  continuous' := λ c, begin
    refine continuous_induced_rng (continuous_pi _),
    intro s',
    simp only [function.comp, map_apply],
    refine continuous.sum' _ _ _,
    rintro s -,
    exact (continuous_apply s).comp continuous_subtype_val,
  end }

@[simps]
def functor (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u} :=
{ obj := λ S, ⟨ℳ p S, λ F, ⟨∥F∥₊, (mem_filtration_iff _ _).mpr le_rfl⟩⟩,
  map := λ S T f, map_hom f,
  map_id' := λ S, by { ext1, rw [map_hom_to_fun, map_id], refl, },
  map_comp' := λ S S' S'' f g, by { ext1, simp only [map_hom_to_fun, map_comp], refl } }

end real_measures
