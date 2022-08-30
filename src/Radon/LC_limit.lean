import Radon.LC_comparison

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

namespace Profinite

/--
This is the cone which will exhibit `X.Radon_LC p c` as the limit of `T.Radon_LC p c`
where `T` varies over the discrete quotients of `X`.
-/
def Radon_LC_cone (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] :
  cone (X.diagram ⋙ Radon_LC_functor p c) :=
(Radon_LC_functor p c).map_cone X.as_limit_cone

namespace is_limit_Radon_LC_cone

variables (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)]

/-- An auxiliary definition to be used in the constructions below. -/
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

variables [fact (p ≤ 1)]

/-- An auxiliary definition to be used in the constructions below. -/
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
  refine le_trans (real.pow_nnnorm_sum_le _ _ _) _,
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

/-- An auxiliary definition to be used in the constructions below. -/
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

/-- `X.Radon_LC_cone p c` is a limit cone, as promised. -/
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

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_LC_CompHaus_diagram (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  discrete_quotient X ⥤ CompHaus.{0} :=
{ obj := λ T, CompHaus.of $ (X.diagram.obj T).Radon_LC p c,
  map := λ S T e, (Radon_LC_functor p c).map $ X.diagram.map e,
  map_id' := begin
    intros T,
    rw X.diagram.map_id,
    rw (Radon_LC_functor p c).map_id,
    refl,
  end,
  map_comp' := begin
    intros S T W f g,
    rw X.diagram.map_comp,
    rw (Radon_LC_functor p c).map_comp,
    refl,
  end }

instance compact_space_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
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

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_LC_CompHaus_functor (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  Profinite.{0} ⥤ CompHaus.{0} :=
{ obj := λ X, CompHaus.of $ X.Radon_LC p c,
  map := λ X Y f, (Radon_LC_functor p c).map f,
  map_id' := (Radon_LC_functor p c).map_id,
  map_comp' := λ X Y Z f g, (Radon_LC_functor p c).map_comp f g }

/--
This is the cone which will exhibit `X.Radon_LC p c` as the limit of `T.Radon_LC p c`
where `T` varies over the discrete quotients of `X`.
This is a variant of `X.Radon_LC_cone` taking values in `CompHaus` as opposed to `Top`.
-/
def Radon_LC_CompHaus_cone (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  cone (X.diagram ⋙ Radon_LC_CompHaus_functor p c) :=
(Radon_LC_CompHaus_functor p c).map_cone X.as_limit_cone

/--
`X.Radon_LC_CompHaus_cone p c` is a limit cone, as promised.
This is another key construction which will be used in the main comparison between
Radon measures and `ℳ_p`.
-/
def is_limit_Radon_LC_CompHaus_cone (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  is_limit (X.Radon_LC_CompHaus_cone p c) :=
begin
  apply is_limit_of_reflects CompHaus_to_Top,
  apply is_limit_Radon_LC_cone,
end

end Profinite
