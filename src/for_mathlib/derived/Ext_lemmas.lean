import for_mathlib.derived.derived_cat
import for_mathlib.derived.example
import for_mathlib.derived.les_facts
import for_mathlib.short_exact
import for_mathlib.derived.ProjectiveResolution

open category_theory category_theory.triangulated category_theory.limits

namespace bounded_derived_category

variables (A : Type*) [category A] [abelian A] [enough_projectives A]

instance Ext_additive_fst (i : ℤ) (X : bounded_derived_category A) :
  (((Ext A i).flip.obj X).right_op).additive :=
{ map_add' := begin
    intros Y Z f g, dsimp,
    conv_rhs { rw ← op_add }, congr' 1, ext e,
    dsimp, rw preadditive.add_comp,
  end }

instance Ext_homological_fst (i : ℤ) (X : bounded_derived_category A) :
  homological_functor ((Ext A i).flip.obj X).right_op :=
category_theory.triangulated.preadditive_yoneda_op_homological (X⟦i⟧)

noncomputable
def Ext'_zero_flip_iso (B : A) :
  (Ext' 0).flip.obj B ≅ (preadditive_yoneda.obj B) :=
iso.symm $
nat_iso.of_components
(λ X, (ProjectiveResolution.of X.unop).Ext_single_iso_hom _)
begin
  intros X Y f, ext F,
  dsimp [ProjectiveResolution.Ext_single_iso_hom,
    ProjectiveResolution.Ext_iso,
    bounded_homotopy_category.Ext_iso,
    ProjectiveResolution.hom_to, Ext',
    bounded_homotopy_category.Ext],
  simp only [comp_apply],
  dsimp,
  simp only [functor.map_comp, category.assoc, bounded_homotopy_category.lift_lifts_assoc],
  /-
  rw [← category.assoc, is_iso.comp_inv_eq],
  simp_rw [category.assoc],
  let t := _, change _ = _ ≫ _ ≫ t,
  let PX := ProjectiveResolution.of X.unop,
  let PY := ProjectiveResolution.of Y.unop,
  let e : PY.complex ⟶ PX.complex := PY.lift f.unop _,
  have ht : t = kernel.lift _ (kernel.ι _ ≫ _) _,
  rotate 2,
  { exact (preadditive_yoneda.obj B).map (e.f 0).op },
  { sorry },
  { sorry },
  rw ht, clear ht, clear t,
  apply equalizer.hom_ext,
  simp only [category.assoc, kernel.lift_ι],
  dsimp only [functor.flip, Ext', functor.comp_map, functor.comp_obj,
    bounded_homotopy_category.Ext, whiskering_left, whisker_left,
    bounded_homotopy_category.Ext0,
    ProjectiveResolution.Ext_single_iso,
    ProjectiveResolution.Ext_iso_zero,
    ProjectiveResolution.Ext_iso,
    ProjectiveResolution.homology_zero_iso,
    bounded_homotopy_category.Ext_iso,
    iso.trans_hom, iso.trans_inv,
    functor.map_iso, iso.op,
    bounded_homotopy_category.replacement_iso,
    nat_iso.app_hom,
    homology_iso, kernel_d_from_iso
    ],
  simp only [category.assoc, equalizer_as_kernel, kernel.lift_ι, kernel.lift_ι_assoc],
  simp only [← functor.map_comp_assoc, ← op_comp, nat_trans.naturality_assoc],
  erw nat_trans.naturality_assoc, congr' 1,
  rw [← functor.map_comp_assoc, ← op_comp],
  let t := _, change _ = _ ≫ t,
  have ht : t = _,


  sorry
  -/
end

-- move me
lemma Ext'_zero_left_is_zero {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  (A : 𝓐ᵒᵖ) (B : 𝓐) (hA : is_zero A) (i : ℤ) :
  is_zero (((Ext' i).obj A).obj B) :=
begin
  rw is_zero_iff_id_eq_zero at hA ⊢,
  rw [← functor.flip_obj_obj, ← category_theory.functor.map_id, hA, functor.map_zero],
end

end bounded_derived_category
