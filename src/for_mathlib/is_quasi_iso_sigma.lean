import for_mathlib.ab4

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A] [has_coproducts A]

namespace homotopy_category

instance is_quasi_iso_sigma [AB4 A] {α : Type v}
  (X : α → homotopy_category A (complex_shape.up ℤ))
  (P : α → homotopy_category A (complex_shape.up ℤ))
  (π : Π a, P a ⟶ X a)
  [∀ a, is_quasi_iso (π a)] :
  is_quasi_iso (sigma.desc $ λ a : α, π a ≫ sigma.ι X a) :=
begin
  constructor, intros i,
  let F := homology_functor _ _ _,
  let t := _, change is_iso (F.map t),
  haveI : preserves_colimits_of_shape (discrete α) F :=
    category_theory.homotopy_category_homology_functor_preserves_coproducts _ _ _ _,
  let eP : F.obj (∐ λ (a : α), P a) ≅ (∐ λ a, F.obj (P a)) :=
    (is_colimit_of_preserves F (colimit.is_colimit _)).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ _, iso.refl _),
  let eX : F.obj (∐ λ (a : α), X a) ≅ (∐ λ a, F.obj (X a)) :=
    (is_colimit_of_preserves F (colimit.is_colimit _)).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ _, iso.refl _),
  let tt : (∐ λ a, F.obj (P a)) ⟶ (∐ λ a, F.obj (X a)) :=
    sigma.desc (λ a : α, F.map (π a) ≫ sigma.ι _ a),
  suffices : F.map t = eP.hom ≫ tt ≫ eX.inv,
  { rw this, apply_instance },
  dsimp [eP, tt, eX],
  apply (is_colimit_of_preserves F (colimit.is_colimit (discrete.functor P))).hom_ext,
  intros i,
  simp only [functor.map_cocone_ι_app, colimit.cocone_ι, category.assoc,
    has_colimit.iso_of_nat_iso_hom_desc_assoc],
  erw (is_colimit_of_preserves F (colimit.is_colimit (discrete.functor P))).fac_assoc,
  rw [← F.map_comp, colimit.ι_desc],
  dsimp,
  simp only [functor.map_comp, colimit.ι_desc_assoc, cocones.precompose_obj_ι,
    nat_trans.comp_app, discrete.nat_iso_hom_app,
    cofan.mk_ι_app, category.assoc, has_colimit.iso_of_nat_iso_ι_inv_assoc,
    discrete.nat_iso_inv_app, colimit.comp_cocone_point_unique_up_to_iso_inv,
    functor.map_cocone_ι_app, colimit.cocone_ι],
  dsimp,
  simp only [category.id_comp],
end

end homotopy_category
