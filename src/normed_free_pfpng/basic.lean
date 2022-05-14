import data.set.intervals
import analysis.mean_inequalities_pow

import for_mathlib.nnreal
import for_mathlib.Profinite.extend
import pseudo_normed_group.category
import condensed.ab

.

open_locale big_operators nnreal

universe u
variables (p : ℝ≥0) (S : Fintype.{u})

/-- The functor represented by ℤ, i.e., sending a finite type `S` to `S → ℤ`,
  equipped with the "p-norm" sending `s ↦ f(s)` to `∑ₛ∥f(s)∥₊ᵖ`. This is the
  construction defined as a bare function. -/
@[derive add_comm_group]
def normed_free_pfpng (p : ℝ≥0) (S : Fintype.{u}) := S → ℤ

noncomputable theory
open_locale classical

instance : has_nnnorm (normed_free_pfpng p S) :=
⟨λ f, ∑ s, ∥f s∥₊ ^ (p:ℝ)⟩

namespace normed_free_pfpng

protected lemma nnnorm_def (f : normed_free_pfpng p S) : ∥f∥₊ = ∑ s, ∥f s∥₊ ^ (p:ℝ) := rfl

@[simp] lemma nnnorm_zero [fact (0 < p)] : ∥(0 : normed_free_pfpng p S)∥₊ = 0 :=
by { change ∑ _, _ = _, simp only [pi.zero_apply, nnnorm_zero, finset.sum_const, nsmul_eq_mul, mul_eq_zero, nat.cast_eq_zero, finset.card_eq_zero,
  nnreal.rpow_eq_zero_iff, eq_self_iff_true, ne.def, nnreal.coe_eq_zero, true_and],
  right, have : 0 < p := fact.out _, exact this.ne' }

@[simp] lemma nnnorm_neg (f : normed_free_pfpng p S) : ∥(-f)∥₊ = ∥f∥₊ :=
by { change ∑ _, _ = _, simpa }

lemma nnnorm_add [fact (0 < p)] [fact (p ≤ 1)]
  (f₁ f₂ : normed_free_pfpng p S) : ∥f₁ + f₂∥₊ ≤ ∥f₁∥₊ + ∥f₂∥₊ :=
begin
  change ∑ _, _ ≤ ∑ _, _ + ∑ _, _,
  rw ← finset.sum_add_distrib,
  apply finset.sum_le_sum,
  intros s _,
  have h0p : 0 < p := fact.out _,
  have hp1 : p ≤ 1 := fact.out _,
  calc ∥(f₁ + f₂) s∥₊ ^ ↑p
      ≤ (∥f₁ s∥₊ + ∥f₂ s∥₊) ^ ↑p : nnreal.rpow_le_rpow (nnnorm_add_le _ _) h0p.le
  ... ≤ ∥f₁ s∥₊ ^ ↑p + ∥f₂ s∥₊ ^ ↑p : nnreal.rpow_add_le_add_rpow _ _ h0p hp1,
end

instance (c) : topological_space { f : normed_free_pfpng p S | ∥f∥₊ ≤ c } := ⊥
instance (c) : discrete_topology { f : normed_free_pfpng p S | ∥f∥₊ ≤ c } := ⟨rfl⟩

lemma norm_eval_le {c : nnreal} (s : S)
  (f : normed_free_pfpng p S) (hf : ∥f∥₊ ≤ c) : ∥f s∥₊ ^ (p:ℝ) ≤ c :=
le_trans (begin
  apply @finset.single_le_sum S nnreal _ (λ t, ∥f t∥₊ ^ (p:ℝ)) finset.univ,
  { intros _ _, apply zero_le },
  { exact finset.mem_univ s }
end) hf

instance [fact (0 < p)] (c) : fintype { f : normed_free_pfpng p S | ∥f∥₊ ≤ c } :=
begin
  let A := { f : normed_free_pfpng p S | ∥f∥₊ ≤ c },
  let N := ⌈c ^ (p⁻¹:ℝ)⌉₊,
  have hN := @nat.le_ceil ℝ≥0 _ _ (c ^ (p⁻¹:ℝ)),
  have h0p : 0 < p := fact.out _,
  have h0pinv : 0 ≤ p⁻¹, { rw ← nnreal.inv_pos at h0p, exact h0p.le },
  let ι : A → S → set.Icc (-(N : ℤ)) N :=
    λ a s, ⟨a.1 s, _⟩,
  swap,
  { have := (nnreal.rpow_le_rpow (norm_eval_le p S s a.val a.2) h0pinv).trans hN,
    rw [← nnreal.coe_le_coe, ← nnreal.rpow_mul, ← nnreal.coe_mul,
      mul_inv_cancel h0p.ne', nnreal.coe_one, nnreal.rpow_one, nnreal.coe_nat_cast] at this,
    split,
    { rw [← neg_le_neg_iff] at this,
      exact_mod_cast this.trans (neg_abs_le_self (a.val s)), },
    { exact_mod_cast (le_abs_self _).trans this, } },
  have : function.injective ι,
  { rintros ⟨f,hf⟩ ⟨g,hg⟩ h,
    ext s,
    apply_fun (λ e, (e s).1) at h,
    assumption },
  apply fintype.of_injective ι this,
end

variables [fact (0 < p)] [fact (p ≤ 1)]

instance : profinitely_filtered_pseudo_normed_group (normed_free_pfpng p S) :=
{ filtration := λ c, { f | ∥ f ∥₊ ≤ c },
  filtration_mono := λ c₁ c₂ h f hf, le_trans hf h,
  zero_mem_filtration := λ c, by simp,
  neg_mem_filtration := λ c f hf, by simpa,
  add_mem_filtration := λ c₁ c₂ f₁ f₂ h₁ h₂,
    le_trans (nnnorm_add _ _ _ _) (add_le_add h₁ h₂),
  continuous_add' := λ c₁ c₂,
    continuous_of_discrete_topology,
  continuous_neg' := λ c, continuous_of_discrete_topology,
  continuous_cast_le := λ _ _ _, continuous_of_discrete_topology,
  ..(infer_instance : add_comm_group (normed_free_pfpng p S)) }

def map {S₁ S₂ : Fintype.{u}} (g : S₁ ⟶ S₂) :
  strict_comphaus_filtered_pseudo_normed_group_hom
  (normed_free_pfpng p S₁) (normed_free_pfpng p S₂) :=
{ to_fun := λ f s, ∑ t in finset.univ.filter (λ w, g w = s), f t,
  map_zero' := by simpa,
  map_add' := λ f g, by simpa [finset.sum_add_distrib],
  strict' := begin
    have h0p : 0 < p := fact.out _,
    have hp1 : p ≤ 1 := fact.out _,
    intros c f hf,
    refine le_trans _ hf,
    simp only [normed_free_pfpng.nnnorm_def],
    have : ∑ s₂, ∥(∑ t in finset.univ.filter (λ w, g w = s₂), f t)∥₊ ^ (p:ℝ) ≤
      ∑ s₂ : S₂, ∑ t in finset.univ.filter (λ w, g w = s₂), ∥f t∥₊ ^ (p:ℝ),
    { apply finset.sum_le_sum,
      intros i _,
      refine le_trans _ (nnreal.rpow_sum_le_sum_rpow _ _ h0p hp1),
      refine nnreal.rpow_le_rpow _ h0p.le,
      apply nnnorm_sum_le },
    refine le_trans this _,
    rw ← finset.sum_bUnion,
    apply le_of_eq,
    apply finset.sum_congr,
    { rw finset.eq_univ_iff_forall,
      intros x,
      rw finset.mem_bUnion,
      use [g x, by simp] },
    { intros s₁ _, refl },
    { intros x _ y _ h,
      rintros a hh,
      apply h,
      simp only [finset.inf_eq_inter, finset.mem_inter, finset.mem_filter,
        finset.mem_univ, true_and] at hh,
      rw [← hh.1, ← hh.2] }
  end,
  continuous' := λ c, continuous_of_discrete_topology }

@[simp]
lemma map_id : map p (𝟙 S) =
  strict_comphaus_filtered_pseudo_normed_group_hom.id :=
begin
  ext s,
  dsimp [map],
  simp [finset.filter_congr_decidable, finset.sum_filter],
end

@[simp]
lemma map_comp {S₁ S₂ S₃ : Fintype.{u}}
  (g₁ : S₁ ⟶ S₂) (g₂ : S₂ ⟶ S₃) :
  map p (g₁ ≫ g₂) =
  (map p g₂).comp (map p g₁) :=
begin
  ext s₃,
  dsimp [map],
  erw ← finset.sum_bUnion,
  apply finset.sum_congr,
  { ext s,
    split,
    { intro h, simp only [finset.mem_filter, finset.mem_univ, true_and] at h,
      rw finset.mem_bUnion,
      use [g₁ s, by simpa] },
    { intro h, simp only [finset.mem_bUnion, finset.mem_filter,
      finset.mem_univ, true_and, exists_prop, exists_eq_right'] at h,
      simpa, } },
  { intros s₁ h,
    rw finset.mem_bUnion at h },
  { intros x hx y hy,
    simp only [finset.coe_filter, finset.coe_univ, set.sep_univ,
      set.mem_set_of_eq] at hx hy,
    intros h a ha,
    simp only [finset.inf_eq_inter, finset.mem_inter, finset.mem_filter,
      finset.mem_univ, true_and] at ha,
    apply h, rw [← ha.1, ← ha.2] }
end

end normed_free_pfpng

variables [fact (0 < p)] [fact (p ≤ 1)]

/-- The functor represented by ℤ, i.e., sending a finite type `S` to
  `normed_free_pfpng p S`, otherwise known as `S → ℤ`,
  equipped with the "p-norm" sending `s ↦ f(s)` to `∑ₛ∥f(s)∥₊ᵖ`. This norm
  makes `S → ℤ` into a `profinitely_filtered_pseudo_normed_group`. -/
@[simps]
def normed_free_pfpng_functor : Fintype ⥤ ProFiltPseuNormGrp₁ :=
{ obj := λ S,
  { M := normed_free_pfpng p S,
    exhaustive' := λ f, ⟨∥f∥₊, le_refl _⟩ },
  map := λ S₁ S₂ f, normed_free_pfpng.map p f,
  map_id' := λ S, normed_free_pfpng.map_id p S,
  map_comp' := λ _ _ _ g₁ g₂, normed_free_pfpng.map_comp p g₁ g₂ }

def Fintype.normed_free_pfpng (T : Fintype) : ProFiltPseuNormGrp₁ :=
(normed_free_pfpng_functor p).obj T

def Fintype.normed_free_pfpng_unit :
  Fintype.to_Profinite ⟶ normed_free_pfpng_functor p ⋙ ProFiltPseuNormGrp₁.level.obj 1 :=
{ app := λ S,
  { to_fun := λ s,
    { val := λ t, if s = t then 1 else 0,
      property := begin
        show finset.sum _ _ ≤ _,
        rw finset.sum_eq_single_of_mem,
        swap 4, { exact s }, swap 2, { apply finset.mem_univ },
        { dsimp, rw [if_pos rfl, nnnorm_one, nnreal.one_rpow], },
        rintro t - ht, dsimp, rw [if_neg ht.symm, nnnorm_zero, nnreal.zero_rpow],
        have h0p : 0 < p := fact.out _, exact_mod_cast h0p.ne',
      end },
    continuous_to_fun := continuous_bot },
  naturality' := λ S T f, begin
    ext s t,
    delta ProFiltPseuNormGrp₁.level,
    simp only [Fintype.to_Profinite_map_to_fun, Profinite.coe_comp, continuous_map.coe_mk,
      function.comp_app, subtype.coe_mk, category_theory.functor.comp_map, normed_free_pfpng_functor_map,
      pseudo_normed_group.level_coe, subtype.coe_mk, normed_free_pfpng.map, finset.mem_filter, true_and,
      finset.mem_univ, strict_comphaus_filtered_pseudo_normed_group_hom.coe_mk, finset.sum_ite_eq],
  end }

def Profinite.normed_free_pfpng (S : Profinite) : ProFiltPseuNormGrp₁ :=
(Profinite.extend $ normed_free_pfpng_functor p).obj S

open category_theory
open category_theory.limits

def Profinite.normed_free_pfpng_level_iso (S : Profinite.{u}) (r) :
  (ProFiltPseuNormGrp₁.level.obj r).obj (S.normed_free_pfpng p) ≅
  limits.limit (S.fintype_diagram ⋙ normed_free_pfpng_functor p ⋙ ProFiltPseuNormGrp₁.level.obj r) :=
(is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj r)
  (limit.is_limit _)).cone_point_unique_up_to_iso $ limit.is_limit _

def Profinite.to_normed_free_pfpng (S : Profinite.{u}) :
  S ⟶ (ProFiltPseuNormGrp₁.level.obj 1).obj (S.normed_free_pfpng p) :=
(limit.is_limit _).map S.as_limit_cone (whisker_left _ $ Fintype.normed_free_pfpng_unit.{u u} p) ≫
(S.normed_free_pfpng_level_iso p 1).inv

--(limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj 1) (limits.limit.is_limit _)).map
--  S.as_limit_cone $ whisker_left _ (Fintype.normed_free_pfpng_unit) ≫ (functor.associator _ _ _).inv

def Profinite.normed_free_pfpng_π (S : Profinite) (T : discrete_quotient S) :
  S.normed_free_pfpng p ⟶ (Fintype.of T).normed_free_pfpng p :=
category_theory.limits.limit.π _ _

lemma Profinite.normed_free_pfpng_π_w (S : Profinite) {T₁ T₂ : discrete_quotient S} (f : T₁ ⟶ T₂) :
  Profinite.normed_free_pfpng_π p S T₁ ≫ (S.fintype_diagram ⋙ normed_free_pfpng_functor p).map f =
  Profinite.normed_free_pfpng_π p S T₂ :=
category_theory.limits.limit.w (S.fintype_diagram ⋙ normed_free_pfpng_functor p) _
