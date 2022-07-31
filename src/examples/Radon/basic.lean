import challenge
import topology.algebra.module.weak_dual
import topology.sets.closeds

open_locale nnreal big_operators

noncomputable theory

open category_theory
open category_theory.limits

namespace discrete_quotient

def equiv_bot (X : Type*) [topological_space X] [discrete_topology X] :
  X ≃ (⊥ : discrete_quotient X) :=
equiv.of_bijective (discrete_quotient.proj _)
⟨λ x y h, quotient.exact' h, quot.mk_surjective _⟩

end discrete_quotient

namespace Profinite

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

variable (X : Profinite.{0})

abbreviation pre_Radon := weak_dual ℝ (C(X,ℝ))
abbreviation pre_Radon_LC := weak_dual ℝ (locally_constant X ℝ)

variable {X}

def indicator {X : Type*} [topological_space X]
  {T : discrete_quotient X} (t : T) : C(X,ℝ) :=
{ to_fun := set.indicator (T.proj ⁻¹' {t}) 1,
  continuous_to_fun := sorry }

lemma indicator_factors {X : Profinite.{0}} {T : discrete_quotient X} (t : T) :
  indicator t = continuous_map.comp
  (indicator $ discrete_quotient.equiv_bot _ t) (X.as_limit_cone.π.app T) :=
begin
  ext a,
  dsimp [indicator, set.indicator],
  split_ifs with h1 h2 h2,
  any_goals { refl },
  { refine false.elim (h2 _),
    rw ← h1, refl },
  { refine false.elim (h1 _),
    obtain ⟨t,rfl⟩ := discrete_quotient.proj_surjective _ t,
    exact quotient.exact' h2 }
end

def indicator_LC {X : Profinite.{0}} {T : discrete_quotient X} (t : T) : locally_constant X ℝ :=
{ to_fun := set.indicator (T.proj ⁻¹' {t}) 1,
  is_locally_constant := sorry }

def pre_Radon.is_bdd (μ : X.pre_Radon) (p c : ℝ≥0) : Prop :=
∀ (T : discrete_quotient X),
  ∑ t : T, (∥ μ (indicator t) ∥₊)^(p : ℝ) ≤ c

def pre_Radon_LC.is_bdd (μ : X.pre_Radon_LC) (p c : ℝ≥0) : Prop :=
∀ (T : discrete_quotient X),
  ∑ t : T, (∥ μ (indicator_LC t) ∥₊)^(p : ℝ) ≤ c

variables (X)

def Radon (p c : ℝ≥0) : Top.{0} :=
Top.of { μ : X.pre_Radon | μ.is_bdd p c }

def Radon_LC (p c : ℝ≥0) : Top.{0} :=
Top.of { μ : X.pre_Radon_LC | μ.is_bdd p c }

variables {X}

def map_C {X Y : Profinite.{0}} (f : X ⟶ Y) :
  C(Y,ℝ) →L[ℝ] C(X,ℝ) :=
{ to_fun := λ g, g.comp f,
  map_add' := λ g1 g2, rfl,
  map_smul' := λ g1 g2, rfl,
  cont := continuous_map.continuous_comp_left f }

def map_LC {X Y : Profinite.{0}} (f : X ⟶ Y) :
  locally_constant Y ℝ →L[ℝ] locally_constant X ℝ :=
{ to_fun := λ g, g.comap f,
  map_add' := sorry,
  map_smul' := sorry,
  cont := sorry }

def map_pre_Radon {X Y : Profinite.{0}} (f : X ⟶ Y) :
  X.pre_Radon →L[ℝ] Y.pre_Radon :=
{ to_fun := λ g, g.comp (map_C f),
  map_add' := λ a b, rfl,
  map_smul' := λ a b, rfl,
  cont := begin
    apply weak_dual.continuous_of_continuous_eval, intros ff,
    apply weak_dual.eval_continuous
  end }

lemma map_pre_Radon_apply {X Y : Profinite.{0}} (f : X ⟶ Y)
  (g : C(Y,ℝ)) (μ : X.pre_Radon) :
  map_pre_Radon f μ g = μ (g.comp f) := rfl

def map_pre_Radon_LC {X Y : Profinite.{0}} (f : X ⟶ Y) :
  X.pre_Radon_LC →L[ℝ] Y.pre_Radon_LC :=
{ to_fun := λ g, g.comp (map_LC f),
  map_add' := λ a b, rfl,
  map_smul' := λ a b, rfl,
  cont := begin
    apply weak_dual.continuous_of_continuous_eval, intros ff,
    apply weak_dual.eval_continuous
  end }

@[simps]
def pre_Radon_functor : Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, Top.of X.pre_Radon,
  map := λ X Y f, ⟨map_pre_Radon f, continuous_linear_map.continuous _⟩,
  map_id' := λ X, by { ext, dsimp [map_pre_Radon], congr, ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

def pre_Radon_LC_functor : Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, Top.of X.pre_Radon_LC,
  map := λ X Y f, ⟨map_pre_Radon_LC f, continuous_linear_map.continuous _⟩,
  map_id' := sorry,
  map_comp' := sorry }

lemma pre_Radon.is_bdd_map {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) (μ : X.pre_Radon) (hμ : μ.is_bdd p c) :
  (map_pre_Radon f μ).is_bdd p c :=
sorry

lemma pre_Radon_LC.is_bdd_map {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) (μ : X.pre_Radon_LC) (hμ : μ.is_bdd p c) :
  (map_pre_Radon_LC f μ).is_bdd p c :=
sorry

def map_Radon {X Y : Profinite.{0}} (f : X ⟶ Y) (p c : ℝ≥0) :
  X.Radon p c ⟶ Y.Radon p c :=
{ to_fun := λ μ, ⟨map_pre_Radon f μ.1, pre_Radon.is_bdd_map f p c μ.1 μ.2⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    apply continuous_linear_map.continuous
  end }

def map_Radon_LC {X Y : Profinite.{0}} (f : X ⟶ Y) (p c : ℝ≥0) :
  X.Radon_LC p c ⟶ Y.Radon_LC p c :=
{ to_fun := λ μ, ⟨map_pre_Radon_LC f μ.1, pre_Radon_LC.is_bdd_map f p c μ.1 μ.2⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    apply continuous_linear_map.continuous
  end }

def Radon_functor (p c) : Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, X.Radon p c,
  map := λ X Y f, map_Radon f _ _,
  map_id' := begin
    intros X, ext, dsimp [map_Radon, map_pre_Radon, map_C],
    congr, ext, refl,
  end,
  map_comp' := begin
    intros X Y Z f g, ext, refl,
  end } .

def Radon_LC_functor (p c) : Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, X.Radon_LC p c,
  map := λ X Y f, map_Radon_LC f _ _,
  map_id' := sorry,
  map_comp' := sorry } .

-- Key calculation 1
def real_measures_iso (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ⋙ CompHaus_to_Top ≅
  Fintype.to_Profinite ⋙ Radon_functor p c := sorry

def LC_to_C (X : Profinite.{0}) : locally_constant X ℝ →L[ℝ] C(X,ℝ) :=
{ to_fun := locally_constant.to_continuous_map,
  map_add' := λ f g, rfl,
  map_smul' := λ f g, rfl,
  cont := (locally_constant.pkg X ℝ).continuous_coe }

def pre_Radon_comparison (X : Profinite.{0}) :
  X.pre_Radon →L[ℝ] X.pre_Radon_LC :=
{ to_fun := λ μ, μ.comp X.LC_to_C,
  map_add' := λ f g, rfl,
  map_smul' := λ f g, rfl,
  cont := begin
    apply weak_dual.continuous_of_continuous_eval, intros ff,
    apply weak_dual.eval_continuous,
  end }

def pre_Radon_comparison_inverse (X : Profinite.{0}) :
  X.pre_Radon_LC →L[ℝ] X.pre_Radon :=
{ to_fun := λ μ,
  { to_fun := λ f, (locally_constant.pkg X ℝ).extend μ f,
    map_add' := sorry,
    map_smul' := sorry,
    cont := sorry },
  map_add' := sorry,
  map_smul' := sorry,
  cont := sorry }

def pre_Radon_equiv (X : Profinite.{0}) :
  X.pre_Radon ≃L[ℝ] X.pre_Radon_LC :=
{ inv_fun := X.pre_Radon_comparison_inverse,
  left_inv := sorry,
  right_inv := sorry,
  continuous_to_fun := X.pre_Radon_comparison.cont,
  continuous_inv_fun := X.pre_Radon_comparison_inverse.cont,
  ..X.pre_Radon_comparison }

def pre_Radon_functor_iso :
  pre_Radon_functor ≅ pre_Radon_LC_functor :=
nat_iso.of_components
(λ X, Top.iso_of_homeo X.pre_Radon_equiv.to_homeomorph)
sorry

def pre_Radon_cone (X : Profinite.{0}) : cone (X.diagram ⋙ pre_Radon_functor) :=
pre_Radon_functor.map_cone X.as_limit_cone

def pre_Radon_limit_comparison (X : Profinite.{0}) :
  Top.of X.pre_Radon ⟶ (Top.limit_cone (X.diagram ⋙ pre_Radon_functor)).X :=
(Top.limit_cone_is_limit _).lift X.pre_Radon_cone

def pre_Radon_LC_cone (X : Profinite.{0}) : cone (X.diagram ⋙ pre_Radon_LC_functor) :=
pre_Radon_LC_functor.map_cone X.as_limit_cone

def pre_Radon_LC_limit_comparison (X : Profinite.{0}) :
  Top.of X.pre_Radon_LC ⟶ (Top.limit_cone (X.diagram ⋙ pre_Radon_LC_functor)).X :=
(Top.limit_cone_is_limit _).lift X.pre_Radon_LC_cone

def pre_Radon_LC_limit_inverse (X : Profinite.{0}) :
  (Top.limit_cone (X.diagram ⋙ pre_Radon_LC_functor)).X ⟶ Top.of X.pre_Radon_LC :=
{ to_fun := λ f,
  { to_fun := λ e,
      let ff := f.1 e.discrete_quotient in
      begin
        dsimp [pre_Radon_LC_functor] at ff,
        exact ff e.locally_constant_lift,
      end,
    map_add' := sorry,
    map_smul' := sorry,
    cont := sorry },
  continuous_to_fun := sorry }

-- TODO: This can be converted into an actual isomoprhism, if needed.
instance is_iso_pre_Radon_LC_limit_comparison (X : Profinite.{0}) :
  is_iso X.pre_Radon_LC_limit_comparison :=
begin
  refine ⟨⟨pre_Radon_LC_limit_inverse X, _, _⟩⟩,
  { ext μ e,
    dsimp [pre_Radon_LC_limit_comparison, pre_Radon_LC_limit_inverse,
      Top.limit_cone_is_limit, pre_Radon_LC_cone, pre_Radon_LC_functor,
      map_pre_Radon_LC, map_LC, as_limit_cone],
    congr' 1, ext a, dsimp [locally_constant.comap],
    rw dif_pos, refl, apply discrete_quotient.proj_continuous },
  { ext μ T e,
    dsimp only [pre_Radon_LC_limit_comparison, pre_Radon_LC_limit_inverse,
      Top.limit_cone_is_limit, pre_Radon_LC_cone, pre_Radon_LC_functor,
      map_pre_Radon_LC, map_LC, as_limit_cone],
    simp only [comp_apply, id_apply],
    dsimp only [continuous_map.coe_mk, functor.map_cone, cones.functoriality,
      subtype.coe_mk],
    dsimp,
    let S := (locally_constant.comap T.proj e).discrete_quotient,
    let W := S ⊓ T,
    let π₁ : W ⟶ S := hom_of_le inf_le_left,
    let π₂ : W ⟶ T := hom_of_le inf_le_right,
    have h1 := μ.2 π₁, have h2 := μ.2 π₂, dsimp only [subtype.val_eq_coe, S] at h1 h2,
    rw [← h1, ← h2], clear h1 h2,
    dsimp [pre_Radon_LC_functor, map_pre_Radon_LC, map_LC, as_limit_cone],
    congr' 1, ext a,
    rw locally_constant.coe_comap,
    rw locally_constant.coe_comap,
    obtain ⟨a,rfl⟩ := discrete_quotient.proj_surjective _ a,
    dsimp only [locally_constant.locally_constant_lift, function.comp_apply,
      locally_constant.coe_mk, Fintype.to_Profinite, fintype_diagram,
      continuous_map.coe_mk],
    rw [discrete_quotient.of_le_proj_apply],
    change ((locally_constant.lift _) ∘ (discrete_quotient.proj _)) _ = _,
    erw [locally_constant.factors],
    rw locally_constant.coe_comap, refl,
    { exact discrete_quotient.proj_continuous _ },
    { exact continuous_bot },
    { exact continuous_bot } },
end

instance is_iso_pre_Radon_comparison (X : Profinite.{0}) :
  is_iso X.pre_Radon_limit_comparison :=
begin
  let E : limit (X.diagram ⋙ pre_Radon_functor) ≅
    limit (X.diagram ⋙ pre_Radon_LC_functor) :=
    has_limit.iso_of_nat_iso (iso_whisker_left _ pre_Radon_functor_iso),
  let e₁ : (Top.limit_cone (X.diagram ⋙ pre_Radon_functor)).X ≅
    limit (X.diagram ⋙ pre_Radon_functor) :=
    (Top.limit_cone_is_limit _).cone_point_unique_up_to_iso (limit.is_limit _),
  let e₂ : (Top.limit_cone (X.diagram ⋙ pre_Radon_LC_functor)).X ≅
    limit (X.diagram ⋙ pre_Radon_LC_functor) :=
    (Top.limit_cone_is_limit _).cone_point_unique_up_to_iso (limit.is_limit _),
  suffices : X.pre_Radon_limit_comparison =
    (pre_Radon_functor_iso.app _).hom ≫
    X.pre_Radon_LC_limit_comparison ≫ e₂.hom ≫ E.inv ≫ e₁.inv,
  { rw this, apply_instance },
  simp only [← category.assoc], simp_rw iso.eq_comp_inv,
  apply limit.hom_ext, intros T,
  dsimp only [e₁, e₂, E, pre_Radon_limit_comparison, pre_Radon_LC_limit_comparison,
    is_limit.cone_point_unique_up_to_iso, cones.forget, functor.map_iso,
    is_limit.unique_up_to_iso, is_limit.lift_cone_morphism, limit.is_limit_lift,
    has_limit.iso_of_nat_iso, is_limit.cone_points_iso_of_nat_iso, is_limit.map,
    cones.postcompose, iso_whisker_left],
  simp only [category.assoc, limit.lift_π, is_limit.fac],
  erw [limit.lift_π_assoc, is_limit.fac_assoc],
  dsimp [pre_Radon_cone, pre_Radon_LC_cone],
  simpa only [nat_trans.naturality],
end

def is_limit_pre_Radon_cone (X : Profinite.{0}) :
  is_limit X.pre_Radon_cone :=
{ lift := λ S, (Top.limit_cone_is_limit _).lift S ≫ inv X.pre_Radon_limit_comparison,
  fac' := begin
    intros S T, rw category.assoc,
    have : inv X.pre_Radon_limit_comparison ≫ (pre_Radon_cone X).π.app T =
      (Top.limit_cone _).π.app _,
    { rw is_iso.inv_comp_eq, erw (Top.limit_cone_is_limit _).fac },
    rw [this, is_limit.fac],
  end,
  uniq' := begin
    intros S m hm,
    rw is_iso.eq_comp_inv,
    apply (Top.limit_cone_is_limit _).uniq,
    exact hm,
  end }
def Radon_cone (p c : ℝ≥0) (X : Profinite.{0}) : cone (X.diagram ⋙ Radon_functor p c) :=
(Radon_functor p c).map_cone X.as_limit_cone

def Radon_comparison (X : Profinite.{0}) (p c : ℝ≥0) :
  X.Radon p c ⟶ (Top.limit_cone (X.diagram ⋙ Radon_functor p c)).X :=
(Top.limit_cone_is_limit _).lift (X.Radon_cone p c)

def Radon_inverse (X : Profinite.{0}) (p c : ℝ≥0) :
  (Top.limit_cone (X.diagram ⋙ Radon_functor p c)).X ⟶ X.Radon p c :=
{ to_fun := λ f, ⟨inv X.pre_Radon_limit_comparison ⟨λ j, (f.1 j).1,
    λ i j e, congr_arg subtype.val (f.2 e)⟩, begin
      intros T,
      convert (f.1 T).2 ⊥ using 1,
      fapply finset.sum_bij',
      { intros a _, exact discrete_quotient.equiv_bot _ a, },
      { intros, exact finset.mem_univ _ },
      { intros a _, congr' 2, dsimp,
        rw [indicator_factors],
        rw ← map_pre_Radon_apply (X.as_limit_cone.π.app T)
          (indicator ((discrete_quotient.equiv_bot T) a)),
        rw [← pre_Radon_functor_map_apply, ← comp_apply],
        have : inv X.pre_Radon_limit_comparison ≫
          pre_Radon_functor.map (X.as_limit_cone.π.app T) =
          (Top.limit_cone _).π.app T,
        { rw is_iso.inv_comp_eq,
          erw (Top.limit_cone_is_limit _).fac, refl },
        rw this, refl },
      { intros a _, exact (discrete_quotient.equiv_bot _).symm a },
      { intros, exact finset.mem_univ _ },
      { intros a _, exact (discrete_quotient.equiv_bot _).symm_apply_apply _ },
      { intros a _, exact (discrete_quotient.equiv_bot _).apply_symm_apply _ },
    end⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp (inv X.pre_Radon_limit_comparison).2 _,
    apply continuous_subtype_mk,
    let f := _, change continuous f,
    have : f =
      (λ g j, _) ∘
      (λ e : (Top.limit_cone (X.diagram ⋙ Radon_functor p c)).X, e.val),
    rotate 2, exact (g j).1,
    refl, rw this, clear this f,
    refine continuous.comp _ continuous_subtype_coe,
    apply continuous_pi, intros j,
    let f := _, change continuous f,
    have : f = subtype.val ∘ (λ e, e j) := rfl, rw this, clear this f,
    exact continuous_subtype_coe.comp (continuous_apply j),
  end }

-- Again, we can give an isomorphism instead of just an `is_iso` instance.
instance is_iso_Radon_comparison (X : Profinite.{0}) (p c : ℝ≥0) :
  is_iso (X.Radon_comparison p c) :=
begin
  use X.Radon_inverse p c,
  split,
  { ext t : 2, dsimp [Radon_inverse],
    apply_fun X.pre_Radon_limit_comparison, rw ← comp_apply,
    rw is_iso.inv_hom_id, refl,
    { intros u v h,
      apply_fun (inv X.pre_Radon_limit_comparison) at h,
      simpa only [← comp_apply, is_iso.hom_inv_id] using h } },
  { ext ⟨t,ht⟩ j : 4, dsimp [Radon_inverse, Radon_comparison,
      Top.limit_cone_is_limit, Radon_cone, Radon_functor, map_Radon],
    change (inv X.pre_Radon_limit_comparison ≫
      pre_Radon_functor.map (X.as_limit_cone.π.app j)) _ = _,
    have : inv X.pre_Radon_limit_comparison ≫
      pre_Radon_functor.map (X.as_limit_cone.π.app j) =
      (Top.limit_cone _).π.app j, by { rw is_iso.inv_comp_eq, ext, refl },
    rw this, refl }
end

-- Key calculation 2: Radon_functor should commute with the limit given by `X.as_limit`.
def is_limit_Radon_cone (p c : ℝ≥0) (X : Profinite.{0}) : is_limit (X.Radon_cone p c) :=
{ lift := λ S, (Top.limit_cone_is_limit _).lift S ≫ inv (X.Radon_comparison p c),
  fac' := begin
    intros S T, rw category.assoc,
    have : inv (X.Radon_comparison p c) ≫ (Radon_cone p c X).π.app T =
      (Top.limit_cone _).π.app _,
    { rw is_iso.inv_comp_eq, erw (Top.limit_cone_is_limit _).fac },
    rw [this, is_limit.fac],
  end,
  uniq' := begin
    intros S m hm,
    rw is_iso.eq_comp_inv,
    apply (Top.limit_cone_is_limit _).uniq,
    exact hm,
  end }

end Profinite
