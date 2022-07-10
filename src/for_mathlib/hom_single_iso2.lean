import for_mathlib.derived.K_projective
import for_mathlib.homological_complex_op
import for_mathlib.homology_iso_Ab
import for_mathlib.hom_single_iso

noncomputable theory

universes v u

open category_theory category_theory.limits category_theory.preadditive

variables {C : Type u} {ι : Type*} [category.{v} C] [abelian C] {c : complex_shape ι}

namespace bounded_homotopy_category

open hom_single_iso_setup opposite

lemma aux₁_naturality_snd_var
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ) (f : B₁ ⟶ B₂) :
  (aux₁ P B₁ i).hom ≫
  (homology_functor AddCommGroup (complex_shape.up ℤ).symm i).map
    ((nat_trans.map_homological_complex (preadditive_yoneda.map f)
    (complex_shape.up ℤ).symm).app P.val.as.op) =
  map_hom_complex_homology _ _ f _ _ ≫ (aux₁ P B₂ i).hom :=
begin
  rw [← iso.comp_inv_eq],
  ext : 2,
  dsimp only [aux₁, iso.symm_hom, iso.symm_inv, homology_iso', homology.map_iso],
  simp only [category.assoc],
  rw [homology.map_eq_desc'_lift_left, homology.π'_desc'_assoc,
    homology.map_eq_lift_desc'_left, homology.lift_ι,
    map_hom_complex_homology,
    homology.map_eq_lift_desc'_left, homology.lift_ι, homology.π'_desc'],
  sorry
end

lemma aux₂_naturality_snd_var
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ) (f : B₁ ⟶ B₂) :
  (aux₂ P B₁ i).inv ≫ P.map_hom_complex_homology i f _ (homological_complex.d_comp_d _ _ _ _) =
  AddCommGroup.homology_map
    (homological_complex.d_comp_d _ _ _ _)
    (homological_complex.d_comp_d _ _ _ _)
    (commsq.of_eq $ ((map_hom_complex' _ f i).comm _ _).symm)
    (commsq.of_eq $ ((map_hom_complex' _ f i).comm _ _).symm) ≫ (aux₂ P B₂ i).inv := sorry

lemma hom_single_iso_naturality_snd_var_good
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ)
  (f : B₁ ⟶ B₂) :
  (hom_single_iso P B₁ i).hom ≫
  (homology_functor _ _ i).map (nat_trans.app (nat_trans.map_homological_complex
    (preadditive_yoneda.map f) _) _) =
  (preadditive_yoneda.map $ (single C i).map f).app (op P) ≫ (hom_single_iso P B₂ i).hom :=
begin
  dsimp only [hom_single_iso, iso.trans_hom, iso.symm_hom, functor.comp_map, functor.op_map,
    functor.right_op_map, quiver.hom.unop_op],
  simp only [category.assoc],
  rw aux₁_naturality_snd_var,
  simp_rw ← category.assoc, congr' 1, simp_rw category.assoc,
  rw aux₂_naturality_snd_var,
  simp_rw ← category.assoc, congr' 1,

  sorry

end

lemma hom_single_iso_naturality_snd_var
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ)
  (f : B₁ ⟶ B₂) (x : P ⟶ (single C i).obj B₁) :
  ((homology_functor _ _ i).map
    ((nat_trans.map_homological_complex (preadditive_yoneda.map f) _).app P.val.as.op))
      ((hom_single_iso P B₁ i).hom x) = ((hom_single_iso P B₂ i).hom (x ≫ (single C i).map f)) :=
begin
  have := hom_single_iso_naturality_snd_var_good P i f,
  apply_fun (λ e, e x) at this,
  exact this
end

end bounded_homotopy_category
