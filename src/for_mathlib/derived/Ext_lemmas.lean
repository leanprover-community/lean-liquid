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
nat_iso.of_components
(λ X, (ProjectiveResolution.of X.unop).Ext_single_iso_hom _)
begin
  intros X Y f,
  dsimp only [ProjectiveResolution.Ext_single_iso_hom,
    ProjectiveResolution.Ext_single_iso_kernel,
    as_iso_hom, iso.trans_hom, iso.symm_hom,
    as_iso_inv],
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
  sorry
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
