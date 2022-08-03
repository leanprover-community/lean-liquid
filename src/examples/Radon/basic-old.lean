import challenge
import topology.algebra.module.weak_dual
import topology.sets.closeds

open_locale nnreal big_operators

noncomputable theory

open category_theory
open category_theory.limits

namespace locally_constant

def comap' {α β γ : Type*} [topological_space α] [topological_space β]
  (f : locally_constant β γ) (g : C(α,β)) : locally_constant α γ :=
{ to_fun := f ∘ g,
  is_locally_constant := begin
    intros S, rw set.preimage_comp, apply is_open.preimage g.2, apply f.2,
  end }

end locally_constant

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

#check (by apply_instance : add_comm_group C(X,ℝ))
#check continuous_map.add_comm_group

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
{ to_fun := λ g, g.comap' f,
  map_add' := λ _ _, by { ext, refl },
  map_smul' := λ _ _, by { ext, refl },
  cont := sorry }

def LC_functor : Profinite.{0}ᵒᵖ ⥤ Top.{0} :=
{ obj := λ X, Top.of $ locally_constant X.unop ℝ,
  map := λ X Y f, ⟨map_LC f.unop, continuous_linear_map.continuous _⟩,
  map_id' := λ _, by { ext, refl },
  map_comp' := λ _ _ _ f g, by { ext, refl } }

def LC_cocone (X : Profinite.{0}) : cocone (X.diagram.op ⋙ LC_functor) :=
LC_functor.map_cocone X.as_limit_cone.op

def is_colimit_LC_cocone (X : Profinite.{0}) : is_colimit X.LC_cocone :=
{ desc := λ S,
  { to_fun := λ f, S.ι.app (opposite.op f.discrete_quotient) f.locally_constant_lift,
    continuous_to_fun := sorry },
  fac' := begin
    intros S T, ext a, dsimp,
    let T' := ((X.LC_cocone.ι.app T) a).discrete_quotient,
    let W := T.unop ⊓ T',
    let π₁ : W ⟶ T.unop := hom_of_le inf_le_left,
    let π₂ : W ⟶ T' := hom_of_le inf_le_right,
    erw [← S.w π₁.op, ← S.w π₂.op],
    dsimp, congr' 1, ext ⟨⟩, refl,
  end,
  uniq' := begin
    intros S m hm,
    ext a, dsimp, rw ← hm, dsimp, congr' 1, ext, refl,
  end }

lemma LC_continuous_iff (X : Profinite.{0}) (Y : Type) [topological_space Y]
  (f : locally_constant X ℝ → Y) :
  continuous f ↔ ∀ T : discrete_quotient X,
  continuous (f ∘ map_LC (X.as_limit_cone.π.app T)) :=
begin
  split,
  { intros hf T,
    refine continuous.comp hf (continuous_linear_map.continuous _) },
  { intros hf,
    let E : cocone (X.diagram.op ⋙ LC_functor) := ⟨Top.of Y, λ T, ⟨_,hf T.unop⟩, _⟩,
    convert ((is_colimit_LC_cocone X).desc E).continuous,
    let h0 : preserves_colimits (forget Top.{0}) := infer_instance,
    letI : preserves_colimit (X.diagram.op ⋙ LC_functor) (forget Top),
    { let h1 := h0.preserves_colimits_of_shape, dsimp at h1,
      let h2 := h1.preserves_colimit,
      exact @h2 (X.diagram.op ⋙ LC_functor) }, -- Why!?!?!?
    apply (is_colimit_of_preserves (forget _) (is_colimit_LC_cocone X)).hom_ext,
    intros T,
    rw ← forget_map_eq_coe,
    erw [← (forget Top.{0}).map_comp, is_colimit.fac], refl,
    { intros T₁ T₂ e,
      ext a, refl, } }
end

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
  map_id' := λ X, by { ext, dsimp [map_pre_Radon_LC, map_LC], congr' 1, ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

lemma pre_Radon.is_bdd_map {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) (μ : X.pre_Radon) (hμ : μ.is_bdd p c) :
  (map_pre_Radon f μ).is_bdd p c :=
sorry

def map_Radon {X Y : Profinite.{0}} (f : X ⟶ Y) (p c : ℝ≥0) :
  X.Radon p c ⟶ Y.Radon p c :=
{ to_fun := λ μ, ⟨map_pre_Radon f μ.1, pre_Radon.is_bdd_map f p c μ.1 μ.2⟩,
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

def pre_Radon_LC_limit_inverse_to_fun_to_fun (X : Profinite.{0})
  (f : ((Top.limit_cone (X.diagram ⋙ pre_Radon_LC_functor)).X)) :
  locally_constant X ℝ → ℝ := λ e,
let ff := f.1 e.discrete_quotient in
begin
  dsimp [pre_Radon_LC_functor] at ff,
  exact ff e.locally_constant_lift,
end

lemma pre_Radon_LC_limit_inverse_to_fun_to_fun_map_add
  (X : Profinite.{0})
  (f : ((Top.limit_cone (X.diagram ⋙ pre_Radon_LC_functor)).X))
  (a b : locally_constant X ℝ) :
  pre_Radon_LC_limit_inverse_to_fun_to_fun X f (a + b) =
  pre_Radon_LC_limit_inverse_to_fun_to_fun X f a +
  pre_Radon_LC_limit_inverse_to_fun_to_fun X f b :=
begin
  dsimp only [pre_Radon_LC_limit_inverse_to_fun_to_fun],
  let Wa := a.discrete_quotient,
  let Wb := b.discrete_quotient,
  let Wab := (a+b).discrete_quotient,
  let W := Wa ⊓ Wb ⊓ Wab,
  let ea : W ⟶ Wa := hom_of_le (le_trans inf_le_left inf_le_left),
  let eb : W ⟶ Wb := hom_of_le (le_trans inf_le_left inf_le_right),
  let eab : W ⟶ Wab := hom_of_le inf_le_right,
  rw [← f.2 ea, ← f.2 eb, ← f.2 eab],
  dsimp [pre_Radon_LC_functor, map_pre_Radon_LC],
  rw ← continuous_linear_map.map_add, congr' 1,
  ext ⟨t⟩, refl,
end
lemma pre_Radon_LC_limit_inverse_to_fun_to_fun_map_smul
  (X : Profinite.{0})
  (f : ((Top.limit_cone (X.diagram ⋙ pre_Radon_LC_functor)).X))
  (a : ℝ)
  (b : locally_constant X ℝ) :
  pre_Radon_LC_limit_inverse_to_fun_to_fun X f (a • b) =
  a • pre_Radon_LC_limit_inverse_to_fun_to_fun X f b :=
begin
  dsimp only [id, pre_Radon_LC_limit_inverse_to_fun_to_fun],
  let Wab := (a • b).discrete_quotient,
  let Wb :=  b.discrete_quotient,
  let W := Wab ⊓ Wb,
  let eab : W ⟶ Wab := hom_of_le inf_le_left,
  let eb : W ⟶ Wb := hom_of_le inf_le_right,
  rw [← f.2 eab, ← f.2 eb],
  dsimp [pre_Radon_LC_functor, map_pre_Radon_LC],
  rw ← smul_eq_mul ℝ,
  erw ← continuous_linear_map.map_smul, congr' 1,
  ext ⟨t⟩, refl,
end

def pre_Radon_LC_limit_inverse (X : Profinite.{0}) :
  (Top.limit_cone (X.diagram ⋙ pre_Radon_LC_functor)).X ⟶ Top.of X.pre_Radon_LC :=
{ to_fun := λ f,
  { to_fun := pre_Radon_LC_limit_inverse_to_fun_to_fun X f,
    map_add' := pre_Radon_LC_limit_inverse_to_fun_to_fun_map_add X f,
    map_smul' := pre_Radon_LC_limit_inverse_to_fun_to_fun_map_smul X f,
    cont := begin
      dsimp only [id, pre_Radon_LC_limit_inverse_to_fun_to_fun],
      rw LC_continuous_iff, intros T,
      convert (f.1 T).continuous using 1,
      ext t,
      dsimp only [function.comp_apply],
      let E := ((map_LC (X.as_limit_cone.π.app T)) t).discrete_quotient ⊓ T,
      let π₁ : E ⟶ ((map_LC (X.as_limit_cone.π.app T)) t).discrete_quotient :=
        hom_of_le inf_le_left,
      let π₂ : E ⟶ T :=
        hom_of_le inf_le_right,
      rw [← f.2 π₁, ← f.2 π₂],
      dsimp [map_LC, pre_Radon_LC_functor, map_pre_Radon_LC],
      congr' 1, ext ⟨x⟩, refl,
    end },
  continuous_to_fun := begin
    dsimp only [id, pre_Radon_LC_limit_inverse_to_fun_to_fun],
    apply weak_dual.continuous_of_continuous_eval, intros ff,
    dsimp,
    let F := _, change continuous F,
    have hF : F = _ ∘ (Top.limit_cone _).π.app ff.discrete_quotient,
    rotate 2,
    { intros μ, exact μ.to_fun ff.locally_constant_lift },
    { refl },
    rw hF, clear hF F, refine continuous.comp _ (continuous_map.continuous _),
    apply weak_dual.eval_continuous
  end }

-- TODO: This can be converted into an actual isomoprhism, if needed.
instance is_iso_pre_Radon_LC_limit_comparison (X : Profinite.{0}) :
  is_iso X.pre_Radon_LC_limit_comparison :=
begin
  refine ⟨⟨pre_Radon_LC_limit_inverse X, _, _⟩⟩,
  { ext μ e,
    dsimp [pre_Radon_LC_limit_comparison, pre_Radon_LC_limit_inverse,
      Top.limit_cone_is_limit, pre_Radon_LC_cone, pre_Radon_LC_functor,
      map_pre_Radon_LC, map_LC, as_limit_cone, pre_Radon_LC_limit_inverse_to_fun_to_fun],
    congr' 1, ext a, refl },
  { ext μ T e,
    dsimp only [pre_Radon_LC_limit_comparison, pre_Radon_LC_limit_inverse,
      Top.limit_cone_is_limit, pre_Radon_LC_cone, pre_Radon_LC_functor,
      map_pre_Radon_LC, map_LC, as_limit_cone, pre_Radon_LC_limit_inverse_to_fun_to_fun],
    simp only [comp_apply, id_apply],
    dsimp only [continuous_map.coe_mk, functor.map_cone, cones.functoriality,
      subtype.coe_mk],
    dsimp,
    let S := (locally_constant.comap' e ⟨T.proj, T.proj_continuous⟩).discrete_quotient,
    let W := S ⊓ T,
    let π₁ : W ⟶ S := hom_of_le inf_le_left,
    let π₂ : W ⟶ T := hom_of_le inf_le_right,
    have h1 := μ.2 π₁, have h2 := μ.2 π₂, dsimp only [subtype.val_eq_coe, S] at h1 h2,
    rw [← h1, ← h2], clear h1 h2,
    dsimp [pre_Radon_LC_functor, map_pre_Radon_LC, map_LC, as_limit_cone],
    congr' 1, ext ⟨a⟩, refl },
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
