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

namespace Profinite

@[derive topological_space]
def Radon (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  Top.{0} :=
Top.of { μ : weak_dual ℝ C(X,ℝ) // μ.bdd p c }

@[derive topological_space]
def Radon_LC (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  Top.{0} :=
Top.of { μ : weak_dual ℝ (locally_constant X ℝ) // μ.bdd_LC p c }

def map_Radon {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ⟶ Y.Radon p c :=
{ to_fun := λ μ, ⟨weak_dual.comap f.comap μ.1,
    weak_dual.bdd_comap _ μ.2 _⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    exact continuous_linear_map.continuous _,
  end }

def map_Radon_LC {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon_LC p c ⟶ Y.Radon_LC p c :=
{ to_fun := λ μ, ⟨weak_dual.comap f.comap_LC μ.1,
    weak_dual.bdd_LC_comap _ μ.2 _⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    exact continuous_linear_map.continuous _,
  end }

def Radon_functor (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, X.Radon p c,
  map := λ X Y f, map_Radon f _ _,
  map_id' := λ X, by { ext, dsimp [map_Radon, weak_dual.comap], congr' 1,
    ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

def Radon_LC_functor (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, X.Radon_LC p c,
  map := λ X Y f, map_Radon_LC f _ _,
  map_id' := λ X,
    by { ext, dsimp [map_Radon_LC, weak_dual.comap], congr' 1, ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

.

def weak_dual_C_to_LC (X : Profinite.{0}) :
  weak_dual ℝ C(X,ℝ) →L[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
weak_dual.comap $ lc_to_c _

def weak_dual_LC_to_C (X : Profinite.{0}) :
  weak_dual ℝ (locally_constant X ℝ) →ₗ[ℝ] weak_dual ℝ C(X,ℝ) :=
{ to_fun := λ f,
  { to_fun := (locally_constant.pkg X ℝ).extend f,
    map_add' := sorry,
    map_smul' := sorry,
    cont := (locally_constant.pkg X ℝ).continuous_extend },
  map_add' := sorry,
  map_smul' := sorry }

def weak_dual_C_equiv_LC (X : Profinite.{0}) :
  weak_dual ℝ C(X,ℝ) ≃ₗ[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
{ inv_fun := X.weak_dual_LC_to_C,
  left_inv := begin
    intros f, ext t,
    dsimp [weak_dual_C_to_LC, weak_dual_LC_to_C],
    apply (locally_constant.pkg X ℝ).induction_on t,
    { apply is_closed_eq,
      apply (locally_constant.pkg X ℝ).continuous_extend,
      apply_instance,
      apply f.2 },
    { intros e,
      rw (locally_constant.pkg X ℝ).extend_coe, refl,
      apply continuous_linear_map.uniform_continuous,
      apply_instance }
  end,
  right_inv := begin
    intros f, ext t,
    dsimp [weak_dual_C_to_LC, weak_dual_LC_to_C,
      weak_dual.comap],
    erw (locally_constant.pkg X ℝ).extend_coe,
    apply continuous_linear_map.uniform_continuous,
    apply_instance,
  end,
--  continuous_to_fun := continuous_linear_map.continuous _,
--  continuous_inv_fun := continuous_linear_map.continuous _,
  ..(X.weak_dual_C_to_LC) }

def Radon_to_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)]:
  X.Radon p c ⟶ X.Radon_LC p c :=
{ to_fun := λ μ, ⟨weak_dual_C_to_LC _ μ.1, μ.2⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    exact continuous_linear_map.continuous _,
  end }

def Radon_LC_to_Radon (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)]:
  X.Radon_LC p c → X.Radon p c :=
λ μ, ⟨weak_dual_LC_to_C _ μ.1, begin
    change (weak_dual_C_to_LC _ (weak_dual_LC_to_C _ μ.1)).bdd_LC p c,
    erw X.weak_dual_C_equiv_LC.apply_symm_apply,
    exact μ.2,
  end⟩

def Radon_LC_to_fun (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon_LC p c → locally_constant X ℝ → ℝ :=
λ μ, μ.1

lemma Radon_LC_to_fun_injective (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  function.injective (X.Radon_LC_to_fun p c) :=
begin
  intros a b h, ext x : 2,
  exact congr_fun h x
end

lemma Radon_LC_to_fun_continuous (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  continuous (X.Radon_LC_to_fun p c) :=
begin
  apply continuous_pi,
  intros f,
  refine continuous.comp (weak_dual.eval_continuous f) (continuous_subtype_coe),
end

--WHY!?!?!?
instance t2_space_LC_to_R (X : Profinite.{0}) :
  t2_space (locally_constant X ℝ → ℝ) :=
@Pi.t2_space (locally_constant X ℝ) (λ _, ℝ) infer_instance
begin
  intros a, dsimp,
  apply_instance
end

instance t2_space_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  t2_space (X.Radon_LC p c) :=
⟨λ f g h, separated_by_continuous (X.Radon_LC_to_fun_continuous p c)
  $ (X.Radon_LC_to_fun_injective p c).ne h⟩

instance compact_space_Radon (X : Profinite) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  compact_space (X.Radon p c) := sorry

def Radon_equiv_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ≃ X.Radon_LC p c :=
{ to_fun := X.Radon_to_Radon_LC p c,
  inv_fun := X.Radon_LC_to_Radon p c,
  left_inv := begin
    intros t, ext1,
    apply X.weak_dual_C_equiv_LC.symm_apply_apply,
  end,
  right_inv := begin
    intros t, ext1,
    apply X.weak_dual_C_equiv_LC.apply_symm_apply,
  end }

lemma continuous_Radon_equiv_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  continuous (X.Radon_equiv_Radon_LC p c) :=
continuous_map.continuous _

lemma continuous_Radon_equiv_Radon_LC_symm (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  continuous (X.Radon_equiv_Radon_LC p c).symm :=
begin
  rw continuous_iff_is_closed,
  intros T hT,
  rw ← equiv.image_eq_preimage,
  apply is_compact.is_closed,
  apply is_compact.image,
  exact is_closed.is_compact hT,
  exact continuous_map.continuous _,
end

def Radon_homeomorph_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ≃ₜ X.Radon_LC p c :=
{ continuous_to_fun := continuous_Radon_equiv_Radon_LC _ _ _,
  continuous_inv_fun := continuous_Radon_equiv_Radon_LC_symm _ _ _,
  ..(X.Radon_equiv_Radon_LC p c) }

def Radon_iso_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ≅ X.Radon_LC p c :=
Top.iso_of_homeo (X.Radon_homeomorph_Radon_LC p c)

def Radon_LC_cone (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  cone (X.diagram ⋙ Radon_LC_functor p c) :=
(Radon_LC_functor p c).map_cone X.as_limit_cone

namespace is_limit_Radon_LC_cone

variables (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)]

def linear_map (S : cone (X.diagram ⋙ Radon_LC_functor p c)) (t : S.X) :
  locally_constant X ℝ →ₗ[ℝ] ℝ :=
{ to_fun := λ e, (S.π.app e.discrete_quotient t).1 e.locally_constant_lift,
  map_add' := begin
    intros e₁ e₂,
    let W₁ := e₁.discrete_quotient,
    let W₂ := e₂.discrete_quotient,
    let W₁₂ := (e₁ + e₂).discrete_quotient,
    let W := W₁ ⊓ W₂ ⊓ W₁₂,
    let π₁ : W ⟶ W₁ := hom_of_le (le_trans inf_le_left inf_le_left),
    let π₂ : W ⟶ W₂ := hom_of_le (le_trans inf_le_left inf_le_right),
    let π₁₂ : W ⟶ W₁₂ := hom_of_le inf_le_right,
    rw [← S.w π₁, ← S.w π₂, ← S.w π₁₂],
    dsimp [Radon_LC_functor, map_Radon_LC, weak_dual.comap, continuous_map.comap_LC],
    erw ← ((S.π.app W) t).1.map_add, congr' 1,
    ext ⟨⟩, refl
  end,
  map_smul' := begin
    intros r e,
    let W₁ := e.discrete_quotient,
    let W₂ := (r • e).discrete_quotient,
    let W := W₁ ⊓ W₂,
    let π₁ : W ⟶ W₁ := hom_of_le inf_le_left,
    let π₂ : W ⟶ W₂ := hom_of_le inf_le_right,
    rw [← S.w π₁, ← S.w π₂],
    dsimp [Radon_LC_functor, map_Radon_LC, weak_dual.comap, continuous_map.comap_LC],
    rw ← smul_eq_mul,
    erw ← ((S.π.app W) t).1.map_smul, congr' 1,
    ext ⟨⟩, refl
  end }

def weak_dual (S : cone (X.diagram ⋙ Radon_LC_functor p c)) (t : S.X) :
  weak_dual ℝ (locally_constant X ℝ) :=
linear_map.mk_continuous_of_exists_bound (linear_map X p c S t)
begin
  use c^(1/(p : ℝ)),
  intros e,
  suffices : ∥ linear_map X p c S t e ∥₊ ≤ c^(1/(p : ℝ)) * ∥ e ∥₊,
    by exact_mod_cast this,
  have hp : 0 < (p : ℝ) := by exact_mod_cast (fact.out (0 < p)),
  have hp' : (p : ℝ) ≠ 0,
  { exact ne_of_gt hp },
  rw [← nnreal.rpow_le_rpow_iff hp, nnreal.mul_rpow, ← nnreal.rpow_mul],
  rw [(show 1 / (p : ℝ) * p = 1, by field_simp), nnreal.rpow_one],
  have H := ((S.π.app e.discrete_quotient) t).2 ⊥,
  replace H := mul_le_mul H (le_refl (∥e∥₊^(p : ℝ))) (zero_le _) (zero_le _),
  refine le_trans _ H,
  rw [mul_comm, finset.mul_sum],
  nth_rewrite 0 e.eq_sum,
  simp_rw [linear_map.map_sum, linear_map.map_smul],
  refine le_trans (real.pow_nnnorm_sum_le _ _) _,
  have : ∑ (x : (⊥ : discrete_quotient e.discrete_quotient)),
    ∥e∥₊ ^ (p : ℝ) * ∥(((S.π.app e.discrete_quotient) t).val)
    ((⊥ : discrete_quotient e.discrete_quotient).fibre x).indicator_LC∥₊ ^ (p : ℝ) =
    ∑ (x : e.discrete_quotient), ∥e∥₊^(p : ℝ) *
      ∥ (linear_map X p c S t) (e.discrete_quotient.fibre x).indicator_LC ∥₊^(p : ℝ),
  { fapply finset.sum_bij',
    { intros a _, exact discrete_quotient.equiv_bot.symm a },
    { intros, exact finset.mem_univ _ },
    { intros, congr' 3, dsimp [linear_map],
      let T₁ := e.discrete_quotient,
      let T₂ := (e.discrete_quotient.fibre
        ((discrete_quotient.equiv_bot.symm) a)).indicator_LC.discrete_quotient,
      let T := T₁ ⊓ T₂,
      let π₁ : T ⟶ T₁ := hom_of_le inf_le_left,
      let π₂ : T ⟶ T₂ := hom_of_le inf_le_right,
      rw [← S.w π₁, ← S.w π₂],
      dsimp [Radon_LC_functor, map_Radon_LC, weak_dual.comap],
      congr' 1,
      ext b, obtain ⟨b,rfl⟩ := discrete_quotient.proj_surjective _ b,
      dsimp [continuous_map.comap_LC],
      change _ =
        (e.discrete_quotient.fibre ((discrete_quotient.equiv_bot.symm) a)).indicator_LC b,
      dsimp only [topological_space.clopens.indicator_LC_apply],
      rw (show X.fintype_diagram.map π₁ (T.proj b) = T₁.proj b, by refl),
      erw discrete_quotient.mem_fibre_iff' },
    { intros a _, exact discrete_quotient.equiv_bot a },
    { intros, exact finset.mem_univ _ },
    { intros, apply equiv.apply_symm_apply },
    { intros, apply equiv.symm_apply_apply } },
  rw this, clear this,
  apply finset.sum_le_sum, rintros x -,
  rw [smul_eq_mul, nnnorm_mul, nnreal.mul_rpow],
  refine mul_le_mul _ (le_refl _) (zero_le _) (zero_le _),
  apply nnreal.rpow_le_rpow _ (le_of_lt hp),
  obtain ⟨x,rfl⟩ := discrete_quotient.proj_surjective _ x,
  change ∥ e x ∥₊ ≤ _,
  apply locally_constant.nnnorm_apply_le_nnnorm,
end

def Radon_LC (S : cone (X.diagram ⋙ Radon_LC_functor p c)) (t : S.X) :
  X.Radon_LC p c :=
{ val := weak_dual X p c S t,
  property := begin
    intros T,
    dsimp [weak_dual, linear_map],
    convert (S.π.app T t).2 ⊥ using 1,
    fapply finset.sum_bij',
    { intros a _, exact discrete_quotient.equiv_bot a },
    { intros, apply finset.mem_univ },
    { intros a ha, congr' 2,
      let W := (T.fibre a).indicator_LC.discrete_quotient,
      let E := T ⊓ W,
      let π₁ : E ⟶ T := hom_of_le inf_le_left,
      let π₂ : E ⟶ W := hom_of_le inf_le_right,
      rw [← S.w π₁, ← S.w π₂],
      dsimp [Radon_LC_functor, map_Radon_LC, weak_dual.comap,
        continuous_map.comap_LC],
      congr' 1, ext b, obtain ⟨b,rfl⟩ := discrete_quotient.proj_surjective _ b,
      change (T.fibre a).indicator_LC b = _,
      dsimp [topological_space.clopens.indicator_LC_apply],
      erw discrete_quotient.mem_fibre_iff },
    { intros a _, exact discrete_quotient.equiv_bot.symm a },
    { intros, apply finset.mem_univ },
    { intros, apply equiv.symm_apply_apply },
    { intros, apply equiv.apply_symm_apply }
  end }

lemma continuous_Radon_LC (S : cone (X.diagram ⋙ Radon_LC_functor p c)) :
  continuous (Radon_LC X p c S) :=
begin
  apply continuous_subtype_mk,
  apply weak_dual.continuous_of_continuous_eval,
  intros e, dsimp [weak_dual, linear_map],
  refine continuous.comp (weak_dual.eval_continuous _) _,
  refine continuous.comp continuous_subtype_coe (continuous_map.continuous _),
end

end is_limit_Radon_LC_cone

def is_limit_Radon_LC_cone (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  is_limit (X.Radon_LC_cone p c) :=
{ lift := λ S, ⟨is_limit_Radon_LC_cone.Radon_LC X p c S,
    is_limit_Radon_LC_cone.continuous_Radon_LC X p c S⟩,
  fac' := begin
    intros S T, ext t e,
    dsimp [Radon_LC_cone, Radon_LC_functor, map_Radon_LC,
      is_limit_Radon_LC_cone.weak_dual, is_limit_Radon_LC_cone.Radon_LC,
      weak_dual.comap, is_limit_Radon_LC_cone.linear_map],
    let W₁ := ((continuous_map.comap_LC (X.as_limit_cone.π.app T)) e).discrete_quotient,
    let W := W₁ ⊓ T,
    let π₁ : W ⟶ W₁ := hom_of_le inf_le_left,
    let π₂ : W ⟶ T := hom_of_le inf_le_right,
    rw [← S.w π₁, ← S.w π₂],
    dsimp [Radon_LC_functor, map_Radon_LC, weak_dual.comap],
    congr' 1, ext ⟨⟩, refl,
  end,
  uniq' := begin
    intros S m hm,
    ext t T,
    specialize hm T.discrete_quotient,
    apply_fun (λ e, (e t).1 T.locally_constant_lift) at hm,
    convert hm using 1,
    dsimp [is_limit_Radon_LC_cone.Radon_LC, is_limit_Radon_LC_cone.weak_dual,
      Radon_LC_cone, Radon_LC_functor, map_Radon_LC, weak_dual.comap],
    congr' 1, ext, refl,
  end }

.

def Radon_LC_comparison (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.diagram ⋙ Radon_LC_functor p c ≅
  X.fintype_diagram ⋙ real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ⋙
  CompHaus_to_Top := sorry

instance compact_space_Radon_LC_of_discrete_quotient (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] (T : discrete_quotient X) :
  compact_space (Radon_LC (X.diagram.obj T) p c) :=
begin
  change compact_space ((X.diagram ⋙ Radon_LC_functor p c).obj T),
  let e := Top.homeo_of_iso ((Radon_LC_comparison X p c).app T),
  haveI : compact_space
    ((X.fintype_diagram ⋙ real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c
    ⋙ CompHaus_to_Top).obj T),
  { change compact_space ((X.fintype_diagram ⋙ real_measures.functor p
      ⋙ CompHausFiltPseuNormGrp₁.level.obj c).obj T), apply_instance },
  exact e.symm.compact_space,
end

def Radon_LC_CompHaus_diagram (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  discrete_quotient X ⥤ CompHaus.{0} :=
{ obj := λ T, CompHaus.of $ (X.diagram.obj T).Radon_LC p c,
  map := λ S T e, (Radon_LC_functor p c).map $ X.diagram.map e,
  map_id' := sorry,
  map_comp' := sorry }

def compact_space_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  compact_space (X.Radon_LC p c) :=
begin
  let e₁ : X.Radon_LC p c ≅ limit (X.diagram ⋙ Radon_LC_functor p c) :=
    (X.is_limit_Radon_LC_cone p c).cone_point_unique_up_to_iso (limit.is_limit _),
  let e₂ :
    CompHaus_to_Top.obj (limit $ X.Radon_LC_CompHaus_diagram p c) ≅
    limit (X.diagram ⋙ Radon_LC_functor p c)  :=
    (is_limit_of_preserves CompHaus_to_Top (limit.is_limit _)).cone_point_unique_up_to_iso
    (limit.is_limit _),
  let e := Top.homeo_of_iso (e₂ ≪≫ e₁.symm),
  haveI : compact_space
    (CompHaus_to_Top.obj (limit $ X.Radon_LC_CompHaus_diagram p c)),
  { show compact_space ↥((limit $ X.Radon_LC_CompHaus_diagram p c)), apply_instance },
  exact e.compact_space,
end

end Profinite
