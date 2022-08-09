import topology.category.Profinite.as_limit
import topology.continuous_function.algebra
import locally_constant.SemiNormedGroup
import locally_constant.completion
import analysis.special_functions.pow
import topology.algebra.module.weak_dual
import analysis.mean_inequalities_pow
import real_measures.condensed

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

lemma real.pow_nnnorm_sum_le
  {ι : Type*} [fintype ι] (r : ι → ℝ)
  (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  ∥ ∑ i, r i ∥₊^(p : ℝ) ≤ ∑ i, ∥ r i ∥₊^(p : ℝ) :=
begin
  refine finset.le_sum_of_subadditive (λ x : ℝ, ∥ x ∥₊^(p : ℝ)) _ _
    (finset.univ : finset ι) r,
  { simp only [nnnorm_zero, nnreal.rpow_eq_zero_iff, eq_self_iff_true, ne.def,
      nnreal.coe_eq_zero, true_and],
    exact ne_of_gt (fact.out _) },
  { intros x y,
    dsimp,
    refine le_trans _ (nnreal.rpow_add_le_add_rpow _ _ _ _),
    rw nnreal.rpow_le_rpow_iff,
    apply nnnorm_add_le,
    any_goals { exact_mod_cast fact.out _ },
    any_goals { assumption } }
end

namespace locally_constant

instance normed_space (X : Type*)
  [topological_space X] [compact_space X] [t2_space X] :
  normed_space ℝ (locally_constant X ℝ) :=
{ norm_smul_le := sorry,
  ..(infer_instance : module ℝ _) }

lemma nnnorm_apply_le_nnnorm (X : Type*)
  [topological_space X] [compact_space X] [t2_space X]
  (e : locally_constant X ℝ) (x : X) :
  ∥ e x ∥₊ ≤ ∥ e ∥₊ :=
begin
  change _ ≤ Sup _,
  apply le_cSup,
  let S := _, change bdd_above S, suffices : is_compact S, apply is_compact.bdd_above this,
  apply is_compact_range, refine continuous.comp _ e.continuous, exact continuous_norm,
  use x, refl,
end

end locally_constant

namespace topological_space.clopens

def indicator {X : Type*} [topological_space X] (U : clopens X) :
  C(X,ℝ) :=
{ to_fun := set.indicator U 1,
  continuous_to_fun := sorry }

def indicator_LC {X : Type*} [topological_space X] (U : clopens X) :
  locally_constant X ℝ :=
{ to_fun := set.indicator U 1,
  is_locally_constant := sorry }

lemma indicator_apply {X : Type*} [topological_space X] (U : clopens X) (x) :
  U.indicator x = if x ∈ U then 1 else 0 := rfl

lemma indicator_LC_apply {X : Type*} [topological_space X] (U : clopens X) (x) :
  U.indicator_LC x = if x ∈ U then 1 else 0 := rfl

end topological_space.clopens

namespace discrete_quotient

def fibre {X : Type*} [topological_space X] (T : discrete_quotient X)
  (t : T) : clopens X :=
{ carrier := T.proj ⁻¹' {t},
  clopen' := sorry }

def equiv_bot {X : Type*} [topological_space X] [discrete_topology X] :
  X ≃ (⊥ : discrete_quotient X) :=
equiv.of_bijective (discrete_quotient.proj _)
⟨λ x y h, quotient.exact' h, discrete_quotient.proj_surjective _⟩

lemma mem_fibre_iff {X : Type*} [topological_space X] [compact_space X] [t2_space X]
  (T : discrete_quotient X) (a : T) (b : X) :
  T.proj b ∈ discrete_quotient.fibre _ (equiv_bot a) ↔
  b ∈ discrete_quotient.fibre T a :=
begin
  obtain ⟨a,rfl⟩ := discrete_quotient.proj_surjective _ a,
  dsimp [fibre, equiv_bot],
  let TT : discrete_quotient T := ⊥,
  change T.proj b ∈ equiv_bot ⁻¹' {equiv_bot (T.proj a)} ↔ T.proj b ∈ {T.proj a},
  simp,
end

lemma mem_fibre_iff' {X : Type*} [topological_space X] [compact_space X] [t2_space X]
  (T : discrete_quotient X) (a : (⊥ : discrete_quotient T)) (b : X) :
  T.proj b ∈ discrete_quotient.fibre _ a ↔
  b ∈ discrete_quotient.fibre T (equiv_bot.symm a) :=
begin
  rw [← equiv_bot.apply_symm_apply a, mem_fibre_iff],
  simp,
end

def comap_equiv {X Y : Type*} [topological_space X] [topological_space Y]
  (f : X → Y) (hf : continuous f) (hf' : function.surjective f)
  (T : discrete_quotient Y) :
  T.comap hf ≃ T :=
equiv.of_bijective (discrete_quotient.map $ le_refl _)
begin
  split,
  { rintros ⟨x⟩ ⟨y⟩ h,
    apply quotient.sound',
    apply quotient.exact' h },
  { rintros ⟨x⟩,
    obtain ⟨x,rfl⟩ := hf' x,
    use discrete_quotient.proj _ x, refl }
end

lemma comap_mem_fibre_iff {X Y : Type*} [topological_space X] [topological_space Y]
  (f : X → Y) (hf : continuous f)
  (T : discrete_quotient Y) (a : T.comap hf) (b : X) :
  b ∈ discrete_quotient.fibre (T.comap hf) a ↔
  f b ∈ discrete_quotient.fibre T (discrete_quotient.map (le_refl _) a) :=
begin
  dsimp [fibre],
  change b ∈ (T.comap hf).proj ⁻¹' {a} ↔
    f b ∈ T.proj ⁻¹' {_},
  obtain ⟨a,rfl⟩ := discrete_quotient.proj_surjective _ a,
  simp only [set.mem_preimage, set.mem_singleton_iff, map_proj_apply],
  split,
  { intros h, apply quotient.sound', apply quotient.exact' h, },
  { intros h, apply quotient.sound', apply quotient.exact' h, },
end

end discrete_quotient

lemma locally_constant.sum_apply {ι X Y : Type*} [topological_space X] [add_comm_monoid Y]
  (f : ι → locally_constant X Y) (S : finset ι) (t : X) :
  (∑ i in S, f i) t = ∑ i in S, (f i t) :=
begin
  let ee : locally_constant X Y →+ X → Y := locally_constant.coe_fn_add_monoid_hom,
  change (ee (∑ i in S, f i)) t = ∑ i in S, (ee (f i) t),
  rw [ee.map_sum, finset.sum_apply],
end

lemma locally_constant.eq_sum {X : Type*} [topological_space X] [compact_space X] [t2_space X]
  (e : locally_constant X ℝ) :
  e = ∑ t : e.discrete_quotient,
    e.locally_constant_lift t • (e.discrete_quotient.fibre t).indicator_LC :=
begin
  ext t,
  simp_rw [locally_constant.sum_apply, locally_constant.smul_apply],
  suffices :
    ∑ (x : ↥(e.discrete_quotient)),
      (e.locally_constant_lift) x • ((e.discrete_quotient.fibre x).indicator_LC) t =
    ∑ x in { e.discrete_quotient.proj t },
      (e.locally_constant_lift) x • ((e.discrete_quotient.fibre x).indicator_LC) t,
  { rw this,
    simp only [algebra.id.smul_eq_mul, finset.sum_singleton],
    change _ = e t * _, symmetry, convert mul_one _,
    rw [topological_space.clopens.indicator_LC_apply, if_pos],
    change e.discrete_quotient.proj t ∈ _, simp, -- clopens is missing some `mem_mk` lemma...
  },
  symmetry,
  apply finset.sum_subset, simp only [finset.subset_univ],
  intros s _ ht,
  convert smul_zero _,
  rw [topological_space.clopens.indicator_LC_apply, if_neg],
  contrapose! ht,
  change e.discrete_quotient.proj t ∈ _ at ht,
  simp only [finset.mem_singleton, set.mem_singleton_iff] at ht ⊢,
  exact ht.symm,
end

def continuous_map.comap {X Y : Type*}
  [topological_space X] [topological_space Y]
  (f : C(X,Y)) : C(Y,ℝ) →L[ℝ] C(X,ℝ) :=
{ to_fun := λ g, g.comp f,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  cont := by refine continuous_map.continuous_comp_left f }

def continuous_map.comap_LC {X Y : Type*}
  [topological_space X] [compact_space X] [t2_space X]
  [topological_space Y] [compact_space Y] [t2_space Y]
  (f : C(X,Y)) : locally_constant Y ℝ →L[ℝ] locally_constant X ℝ :=
{ to_fun := λ g,
  { to_fun := g ∘ f,
    is_locally_constant := λ S,
      by { rw set.preimage_comp, apply is_open.preimage f.2, apply g.2, } },
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  cont := sorry }

def lc_to_c (X : Type*)
  [topological_space X] [compact_space X] [t2_space X] :
  locally_constant X ℝ →L[ℝ] C(X,ℝ) :=
{ to_fun := λ f, f.to_continuous_map,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  cont := begin
    apply isometry.continuous,
    intros f g,
    simp only [edist_dist, dist_eq_norm, continuous_map.norm_eq_supr_norm,
      locally_constant.norm_def, locally_constant.to_continuous_map_eq_coe,
      continuous_map.coe_sub, locally_constant.coe_continuous_map, pi.sub_apply],
    refl,
  end }

namespace weak_dual

def comap {A B : Type*}
  [add_comm_group A] [module ℝ A] [topological_space A]
  [add_comm_group B] [module ℝ B] [topological_space B]
  (f : A →L[ℝ] B) :
  weak_dual ℝ B →L[ℝ] weak_dual ℝ A :=
{ to_fun := λ g, g.comp f,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  cont := begin
    apply weak_dual.continuous_of_continuous_eval,
    intros a,
    apply weak_dual.eval_continuous,
  end }

def bdd {X : Type*} [topological_space X] [compact_space X]
  (μ : weak_dual ℝ C(X,ℝ)) (p c : ℝ≥0) : Prop :=
∀ (T : discrete_quotient X),
  ∑ t : T, ∥ μ (T.fibre t).indicator ∥₊^(p : ℝ) ≤ c

def bdd_LC {X : Type*} [topological_space X] [compact_space X]
  (μ : weak_dual ℝ (locally_constant X ℝ)) (p c : ℝ≥0) : Prop :=
∀ (T : discrete_quotient X),
  ∑ t : T, ∥ μ (T.fibre t).indicator_LC ∥₊^(p : ℝ) ≤ c

lemma bdd_LC_comap {X Y : Type*} {p c : ℝ≥0} [fact (0 < p)]
  [topological_space X] [compact_space X] [t2_space X]
  [topological_space Y] [compact_space Y] [t2_space Y]
  (μ : weak_dual ℝ (locally_constant X ℝ)) (hμ : μ.bdd_LC p c) (f : C(X,Y)) :
  (weak_dual.comap f.comap_LC μ).bdd_LC p c :=
begin
  intros T,
  convert hμ (T.comap f.2) using 1,
  let ι : T.comap f.2 → T := discrete_quotient.map (le_refl _),
  have hι : function.injective ι,
  { rintros ⟨⟩ ⟨⟩ h,
    apply quotient.sound',
    apply quotient.exact' h },
  let S₁ := _, change S₁ = _,
  have : S₁ = ∑ t in finset.univ.image ι,
    ∥ ((comap f.comap_LC) μ) (T.fibre t).indicator_LC ∥₊ ^ (p : ℝ),
  { symmetry, apply finset.sum_subset, simp,
    intros x _ hx,
    --simp only [finset.mem_image, finset.mem_univ, exists_true_left, not_exists] at hx,
    suffices : ((comap f.comap_LC) μ) (T.fibre x).indicator_LC = 0,
    { simp only [this, nnnorm_zero, nnreal.rpow_eq_zero_iff, eq_self_iff_true,
        ne.def, nnreal.coe_eq_zero, true_and],
      exact ne_of_gt (fact.out (0 < p)) },
    dsimp [comap], convert μ.map_zero,
    ext t,
    dsimp [continuous_map.comap_LC, topological_space.clopens.indicator_LC_apply],
    rw if_neg,
    contrapose! hx,
    rw finset.mem_image,
    refine ⟨discrete_quotient.proj _ t, finset.mem_univ _, hx⟩,
  },
  rw this, clear this, symmetry,
  fapply finset.sum_bij,
  { intros a _, exact ι a },
  { intros, dsimp, erw finset.mem_image, refine ⟨a, finset.mem_univ _, rfl⟩ },
  { intros a ha, congr' 2,
    dsimp [comap], congr' 1,
    ext t,
    erw topological_space.clopens.indicator_LC_apply,
    erw topological_space.clopens.indicator_LC_apply,
    rw discrete_quotient.comap_mem_fibre_iff },
  { intros a₁ a₂ h₁ h₂ hh, apply hι, exact hh },
  { rintros b hb,
    rw finset.mem_image at hb,
    obtain ⟨b,hh,hb⟩ := hb,
    use [b,hh,hb.symm] },
end

lemma bdd_comap {X Y : Type*} {p c : ℝ≥0} [fact (0 < p)]
  [topological_space X] [compact_space X] [t2_space X]
  [topological_space Y] [compact_space Y] [t2_space Y]
  (μ : weak_dual ℝ C(X,ℝ)) (hμ : μ.bdd p c) (f : C(X,Y)) :
  (weak_dual.comap f.comap μ).bdd p c :=
λ t, by apply bdd_LC_comap (comap (lc_to_c X) μ) hμ f t

end weak_dual
