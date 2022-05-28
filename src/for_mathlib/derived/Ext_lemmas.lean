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
end

-- move me
lemma Ext'_zero_left_is_zero {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  (A : 𝓐ᵒᵖ) (B : 𝓐) (hA : is_zero A) (i : ℤ) :
  is_zero (((Ext' i).obj A).obj B) :=
begin
  rw is_zero_iff_id_eq_zero at hA ⊢,
  rw [← functor.flip_obj_obj, ← category_theory.functor.map_id, hA, functor.map_zero],
end

lemma Ext'_is_zero_of_projective {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  (A B : 𝓐) (hA : projective A) (i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (opposite.op A)).obj B) :=
begin
  let := Ext'_iso (opposite.op A) B i,
  dsimp at this,
  refine is_zero_of_iso_of_zero _ (this _ (𝟙 _) _).symm,
  swap,
  { refine ⟨_, _, _⟩,
    { rintro (_|n), { exact hA }, { exact projective_zero } },
    { apply exact_zero_left_of_mono, },
    { intro, apply exact_zero_left_of_mono, } },
  rcases i with ((_|i)|i),
  { exfalso, revert hi, dec_trivial },
  swap,
  { exfalso, revert hi, dec_trivial },
  refine is_zero.homology_is_zero _ _ _ _,
  refine AddCommGroup.is_zero_of_eq _ _,
  intros f g,
  apply category_theory.limits.has_zero_object.from_zero_ext
end

end bounded_derived_category
