import Radon.LC_limit
import analysis.normed_space.weak_dual

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

namespace Profinite

/-- The weak dual of `C(X,ℝ)` is linearly equivalent to
the weak dual of `locally_constant X ℝ`. -/
def weak_dual_C_equiv_LC (X : Profinite.{0}) :
  weak_dual ℝ C(X,ℝ) ≃ₗ[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
{ inv_fun := X.weak_dual_LC_to_C,
  left_inv := begin
    intros f, ext t,
    show (locally_constant.pkg X ℝ).extend _ _ = _,
    --  `dsimp [weak_dual_C_to_LC, weak_dual_LC_to_C]` works instead of `show` but is slower
    apply (locally_constant.pkg X ℝ).induction_on t,
    { apply is_closed_eq,
      refine (locally_constant.pkg X ℝ).continuous_extend,
      exact f.2 },
    { intros e,
      rw (locally_constant.pkg X ℝ).extend_coe, refl,
      apply continuous_linear_map.uniform_continuous,
      apply_instance }
  end,
  right_inv := begin
    intros f, ext t,
    show (locally_constant.pkg X ℝ).extend _ _ = _,
--  `dsimp [weak_dual_C_to_LC, weak_dual_LC_to_C, weak_dual.comap]` works instead of `show`,
--  but is slower,
    erw (locally_constant.pkg X ℝ).extend_coe,
    apply continuous_linear_map.uniform_continuous,
    apply_instance,
  end,
  ..(X.weak_dual_C_to_LC) }

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_to_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0) :
  X.Radon p c ⟶ X.Radon_LC p c :=
{ to_fun := λ μ, ⟨weak_dual_C_to_LC _ μ.1, μ.2⟩,
  continuous_to_fun := begin
    apply continuous.subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    exact continuous_linear_map.continuous _,
  end }

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_LC_to_Radon (X : Profinite.{0}) (p c : ℝ≥0) :
  X.Radon_LC p c → X.Radon p c :=
λ μ, ⟨weak_dual_LC_to_C _ μ.1, begin
    change (weak_dual_C_to_LC _ (weak_dual_LC_to_C _ μ.1)).bdd_LC p c,
    erw X.weak_dual_C_equiv_LC.apply_symm_apply,
    exact μ.2,
  end⟩

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_LC_to_weak_dual (X : Profinite.{0}) (p c : ℝ≥0) :
  X.Radon_LC p c → weak_dual ℝ (locally_constant X ℝ) := subtype.val

/-- An auxiliary definition to be used in the constructions below. -/
def weak_dual_LC_to_fun (X : Profinite.{0}) :
  weak_dual ℝ (locally_constant X ℝ) → locally_constant X ℝ → ℝ := λ μ x, μ x

lemma continuous_weak_dual_LC_to_fun (X : Profinite.{0}) :
  continuous X.weak_dual_LC_to_fun :=
begin
  apply continuous_pi, intros e,
  exact weak_dual.eval_continuous _,
end

instance t2_space_weak_dual (X : Profinite.{0}) :
  t2_space (weak_dual ℝ (locally_constant X ℝ)) :=
⟨λ x y h, separated_by_continuous (X.continuous_weak_dual_LC_to_fun) $
  λ c, h $ by { ext t, apply_fun (λ e, e t) at c, exact c } ⟩

lemma Radon_LC_closed_embedding (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  closed_embedding (X.Radon_LC_to_weak_dual p c) :=
closed_embedding_subtype_coe
begin
  apply is_compact.is_closed,
  let S := _, change is_compact S,
  have : S = set.range (X.Radon_LC_to_weak_dual p c),
  { erw subtype.range_val, refl },
  rw this, clear this,
  apply is_compact_range,
  exact continuous_subtype_coe,
end

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_to_weak_dual (X : Profinite.{0}) (p c : ℝ≥0) :
  X.Radon p c → weak_dual ℝ C(X,ℝ) := subtype.val

lemma Radon_closed_embedding (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  closed_embedding (X.Radon_to_weak_dual p c) :=
closed_embedding_subtype_coe
begin
  let T : set (weak_dual ℝ (locally_constant X ℝ)) :=
    { f | f.bdd_LC p c },
  change is_closed (X.weak_dual_C_to_LC ⁻¹' T),
  apply is_closed.preimage,
  exact (weak_dual_C_to_LC X).continuous,
  convert (X.Radon_LC_closed_embedding p c).closed_range,
  erw subtype.range_val, refl,
end

lemma Radon_closed_embedding_range_bdd (X : Profinite) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] : metric.bounded
  (normed_space.dual.to_weak_dual ⁻¹' set.range (X.Radon_to_weak_dual p c)) :=
begin
  -- Use c^(1/p)
  letI : uniform_space (locally_constant.pkg X ℝ).space :=
    (locally_constant.pkg X ℝ).uniform_struct,
  refine (metric.bounded_iff_subset_ball 0).mpr _,
  refine ⟨c^(1/(p : ℝ)), λ μ hμ, mem_closed_ball_zero_iff.mpr _⟩,
  apply continuous_linear_map.op_norm_le_bound,
  refine (nnreal.coe_nonneg _).trans_eq (nnreal.coe_rpow _ _),
  intros f,
  apply (locally_constant.pkg X ℝ).induction_on f,
  { apply is_closed_le,
    refine continuous.comp (continuous_norm) _,
    exact μ.continuous,
    refine continuous.comp (continuous_mul_left _) continuous_norm },
  { intros e,
    let γ : weak_dual ℝ (locally_constant X ℝ) :=
      X.weak_dual_C_to_LC μ,
    dsimp [locally_constant.pkg],
    have : μ e = γ e, refl, rw this, clear this,
    have : ∥ e.to_continuous_map ∥ = ∥ e ∥,
    { simp only [continuous_map.norm_eq_supr_norm,
        locally_constant.norm_def, locally_constant.to_continuous_map_eq_coe,
        locally_constant.coe_continuous_map] },
    erw this, clear this,
    suffices : ∥ γ e ∥₊ ≤ c^(1 / (p : ℝ)) * ∥ e ∥₊, by exact_mod_cast this,
    have hp : 0 < (p : ℝ) := nnreal.coe_pos.mpr (fact.out (0 < p)),
    have hp' : (p : ℝ) ≠ 0,
    { exact ne_of_gt hp },
    rw [← nnreal.rpow_le_rpow_iff hp, nnreal.mul_rpow, ← nnreal.rpow_mul],
    rw [(show 1 / (p : ℝ) * p = 1, from (eq_div_iff hp').mp rfl), nnreal.rpow_one],
    obtain ⟨δ,hδ⟩ := hμ,
    have H := δ.2 e.discrete_quotient,
    replace H := mul_le_mul H (le_refl (∥ e ∥₊^(p : ℝ))) (zero_le _) (zero_le _),
    refine le_trans _ H, clear H,
    rw [mul_comm, finset.mul_sum],
    nth_rewrite 0 e.eq_sum,

    simp_rw [γ.map_sum, γ.map_smul],
    refine le_trans (real.pow_nnnorm_sum_le _ _ _) _,

    apply finset.sum_le_sum, rintros x -,
    rw [smul_eq_mul, nnnorm_mul, nnreal.mul_rpow],
    refine mul_le_mul _ (le_of_eq _) (zero_le _) (zero_le _),
    apply nnreal.rpow_le_rpow _ (le_of_lt hp),
    obtain ⟨x,rfl⟩ := discrete_quotient.proj_surjective _ x,
    change ∥ e x ∥₊ ≤ _,
    apply locally_constant.nnnorm_apply_le_nnnorm,
    congr' 2,
    change _ = X.Radon_to_weak_dual p c δ _, rw hδ, refl },
end

instance compact_space_Radon (X : Profinite) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  compact_space (X.Radon p c) :=
begin
  let e : X.Radon p c ≃ₜ set.range (X.Radon_to_weak_dual p c) :=
    homeomorph.of_embedding _ (X.Radon_closed_embedding p c).to_embedding,
  suffices : compact_space (set.range (X.Radon_to_weak_dual p c)),
  { resetI, apply e.symm.compact_space },
  rw ← is_compact_iff_compact_space,
  apply weak_dual.is_compact_of_bounded_of_closed,
  apply Radon_closed_embedding_range_bdd,
  exact (X.Radon_closed_embedding p c).closed_range,
end

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_equiv_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0) :
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

lemma continuous_Radon_equiv_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0) :
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

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_homeomorph_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ≃ₜ X.Radon_LC p c :=
{ continuous_to_fun := continuous_Radon_equiv_Radon_LC _ _ _,
  continuous_inv_fun := continuous_Radon_equiv_Radon_LC_symm _ _ _,
  ..(X.Radon_equiv_Radon_LC p c) }

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_iso_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ≅ X.Radon_LC p c :=
Top.iso_of_homeo (X.Radon_homeomorph_Radon_LC p c)

/-- The functor `X ↦ X.Radon p c` is isomorphic to its locally constant variant. -/
def Radon_functor_iso_Radon_LC_functor (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  Radon_functor p c ≅ Radon_LC_functor p c :=
nat_iso.of_components
(λ X, X.Radon_iso_Radon_LC p c)
begin
  intros X Y f, ext, refl,
end

/-- A `CompHaus` variant of `Radon_functor`. -/
def Radon_CompHaus_functor (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  Profinite.{0} ⥤ CompHaus.{0} :=
{ obj := λ X, CompHaus.of $ X.Radon p c,
  map := λ X Y f, (Radon_functor p c).map f,
  map_id' := (Radon_functor p c).map_id,
  map_comp' := λ _ _ _ f g, (Radon_functor p c).map_comp f g }

/-- The functor `X ↦ X.Radon p c` is isomorphic to its locally constant variant.
This is a variant taking values in `CompHaus` as opposed to `Top`. -/
def Radon_CompHaus_functor_iso_Radon_LC_CompHaus_functor (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  Radon_CompHaus_functor p c ≅ Radon_LC_CompHaus_functor p c :=
nat_iso.of_components
(λ X,
{ hom := (Radon_functor_iso_Radon_LC_functor p c).hom.app X,
  inv := (Radon_functor_iso_Radon_LC_functor p c).inv.app X,
  hom_inv_id' := begin
    erw [← nat_trans.comp_app, iso.hom_inv_id], refl,
  end,
  inv_hom_id' := begin
    erw [← nat_trans.comp_app, iso.inv_hom_id], refl,
  end })
begin
  intros, ext, refl,
end

/-- The cone exhibiting `X.Radon p c` as the limit of `T.Radon p c` where
`T` varies over the discrete quotients of `X`. -/
def Radon_CompHaus_cone (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  cone (X.diagram ⋙ Radon_CompHaus_functor p c) :=
(Radon_CompHaus_functor p c).map_cone X.as_limit_cone

/-- X.Radon_CompHaus_cone p c` is a limit cone, as promised. -/
def is_limit_Radon_CompHaus_cone (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  is_limit (X.Radon_CompHaus_cone p c) :=
{ lift := λ S,
    (X.is_limit_Radon_LC_CompHaus_cone p c).lift
    ⟨S.X, S.π ≫ whisker_left _ (Radon_CompHaus_functor_iso_Radon_LC_CompHaus_functor p c).hom⟩ ≫
    (Radon_CompHaus_functor_iso_Radon_LC_CompHaus_functor p c).inv.app _,
  fac' := begin
    intros S j,
    erw [category.assoc, ← nat_trans.naturality,
      (X.is_limit_Radon_LC_CompHaus_cone p c).fac_assoc,
      ← nat_iso.app_inv, iso.comp_inv_eq], refl,
  end,
  uniq' := begin
    intros S m hm,
    rw [← nat_iso.app_inv, iso.eq_comp_inv],
    apply (X.is_limit_Radon_LC_CompHaus_cone p c).hom_ext, intros j,
    erw (X.is_limit_Radon_LC_CompHaus_cone p c).fac,
    dsimp, rw ← hm,
    simp only [category.assoc],
    erw ← nat_trans.naturality,
  end }

/-- The comparison between `Radon_LC` and `real_measures p` taking
values in `CompHaus` instead of `Top`, and restricted to the discrete quotients of `X`. -/
def Radon_LC_CompHaus_comparison (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.diagram ⋙ Radon_LC_CompHaus_functor p c ≅
  X.fintype_diagram ⋙ real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c :=
nat_iso.of_components
(λ T,
{ hom := (X.Radon_LC_comparison p c).hom.app _,
  inv := (X.Radon_LC_comparison p c).inv.app _,
  hom_inv_id' := begin
    erw [← nat_trans.comp_app, iso.hom_inv_id], refl,
  end,
  inv_hom_id' := begin
    erw [← nat_trans.comp_app, iso.inv_hom_id], refl,
  end })
begin
  intros S T i, dsimp,
  erw ((X.Radon_LC_comparison p c).hom).naturality, refl,
end

/-- The comparison between `Radon` and `real_measures p`
restricted to the discrete quotients of `X`. -/
def Radon_CompHaus_comparison (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.diagram ⋙ Radon_CompHaus_functor p c ≅
  X.fintype_diagram ⋙ real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c :=
iso_whisker_left _ (Radon_CompHaus_functor_iso_Radon_LC_CompHaus_functor _ _) ≪≫
Radon_LC_CompHaus_comparison _ _ _

/-- An auxiliary definition to be used in the constructions below. -/
def Radon_iso_limit (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  CompHaus.of (X.Radon p c) ≅
  limit (X.fintype_diagram ⋙ real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c) :=
(X.is_limit_Radon_CompHaus_cone p c).cone_point_unique_up_to_iso (limit.is_limit _) ≪≫
has_limit.iso_of_nat_iso (Radon_CompHaus_comparison _ _ _)

/-- The compact Hausdorff space `X.Radon p c` is isomorphic to the limit of
`real_measures p T` as `T` varies over the discrete quotients of `X`.
-/
def Radon_iso_real_measures (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  CompHaus.of (X.Radon p c) ≅
  (CompHausFiltPseuNormGrp₁.level.obj c).obj
  ((Profinite.extend (real_measures.functor p)).obj X) :=
Radon_iso_limit _ _ _ ≪≫
has_limit.iso_of_nat_iso (functor.associator _ _ _).symm ≪≫
(limit.is_limit _).cone_point_unique_up_to_iso
(is_limit_of_preserves ((CompHausFiltPseuNormGrp₁.level.obj c))
  (limit.is_limit (X.fintype_diagram ⋙ real_measures.functor p)))

end Profinite
