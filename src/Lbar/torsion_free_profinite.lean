import algebra.category.Group.limits
import for_mathlib.Profinite.extend
import Lbar.basic
import Lbar.functor
import pseudo_normed_group.category.strictProFiltPseuNormGrpWithTinv
import pseudo_normed_group.bounded_limits

noncomputable theory

universes u v

open_locale nnreal


set_option pp.universes true

open Lbar Profinite CommGroup category_theory.limits

lemma limit_torsion_free_to_Ab
  (C : Type u) [category_theory.small_category C] (J : C ⥤ Ab.{u})
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (limit J).α :=
begin
  let L := get_limit_cone _,
  haveI := AddCommGroup.forget_preserves_limits.{u u},
  have h_inj := @concrete.to_product_injective_of_is_limit AddCommGroup.{u} _ _
    C _ J _ L.cone L.is_limit,
  fconstructor,
  intros c x hx,
  let φ := λ x : (limit J), λ j, (L.cone.π.app j) x,
  have h1: φ 0 = 0,
  { ext j,
    exact (L.cone.π.app j).2 },
  have h2: φ (c • x) = c • φ x,
  { ext j,
    exact map_zsmul (L.cone.π.app j) _ _ },
  apply_fun φ at hx,
  simp only [h1, h2, pi.zero_def, function.funext_iff, pi.smul_apply, smul_eq_zero] at hx,
  by_cases hc : c = 0,
  { apply or.intro_left, exact hc},
  { simp only [hc, false_or] at hx,
    apply or.intro_right,
    apply h_inj,
    funext j,
    specialize hx j,
    simp only [_root_.map_zero],
    exact hx },
end

--[FAE] not needed for LTE, may be for mathlib?
lemma add_comm_group.limit_on_nat_torsion_free
  (J : (category_theory.as_small.{u} ℕ) ⥤ AddCommGroup.{u})
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (limit J).α := limit_torsion_free_to_Ab (category_theory.as_small.{u} ℕ) J h_tf

open CompHausFiltPseuNormGrp₁

lemma PNG₁.iso_injective {X Y : PseuNormGrp₁} (f : X ≅ Y) :
  function.injective f.hom :=
sorry

lemma PNG₁.map_zsmul {X Y : PseuNormGrp₁} (f : X ⟶ Y) (n : ℤ) (x : X) :
  f (n • x) = n • f x :=
f.to_add_monoid_hom.map_zsmul _ _

namespace Profinite

lemma extend_torsion_free (A : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁)
  (hA : ∀ X, no_zero_smul_divisors ℤ (A.obj X)) (S : Profinite) :
  no_zero_smul_divisors ℤ ((Profinite.extend A).obj S) :=
begin
  let T := Ab.explicit_limit_cone.{u u}
    ((S.fintype_diagram ⋙ A ⋙ to_PNG₁) ⋙ PseuNormGrp₁.to_Ab),
  let hT : is_limit T := Ab.explicit_limit_cone_is_limit _,
  let E := PseuNormGrp₁.bounded_cone.{u} ⟨T,hT⟩,
  let hE : is_limit E := PseuNormGrp₁.bounded_cone_is_limit _,
  suffices claim : no_zero_smul_divisors ℤ E.X,
  { resetI,
    let iso : to_PNG₁.obj ((extend (A)).obj S) ≅ E.X :=
      (is_limit_of_preserves to_PNG₁
      (limit.is_limit _)).cone_point_unique_up_to_iso hE,
    apply function.injective.no_zero_smul_divisors iso.hom (PNG₁.iso_injective _),
    any_goals { apply_instance },
    { apply strict_pseudo_normed_group_hom.map_zero },
    { intros, rw PNG₁.map_zsmul } },
  let ι : E.X →+ T.X := add_subgroup.subtype _,
  apply function.injective.no_zero_smul_divisors ι (subtype.val_injective.{u+1}) ι.map_zero,
  any_goals { apply_instance },
  { intros c x, apply ι.map_zsmul, },
  sorry,
  --At this point, we have to show that the point of the explicit limit cone of plain
  --abelian groups is torsion-free. This should already be defeq to a subtype of the product!
  --The finite case should then give us the result.
end

end Profinite
