import algebra.homology.homology
import category_theory.limits.shapes.zero_objects
import category_theory.abelian.homology

import for_mathlib.homology_exact

noncomputable theory

open category_theory category_theory.limits

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

section

lemma exact_iff_image_to_kernel'_is_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  exact f g ↔ is_iso (image_to_kernel' f g w) :=
begin
  refine ⟨λ h, _, λ h, ⟨w, _⟩⟩,
  { suffices : is_iso (image_to_kernel f g w),
    { have hiso : is_iso (image_to_kernel f g w ≫
      (category_theory.limits.kernel_subobject_iso g).hom) := by exactI is_iso.comp_is_iso,
      rw [← image_subobject_iso_image_to_kernel'] at hiso,
      exactI is_iso.of_is_iso_comp_left (image_subobject_iso f).hom _ },
    exact image_to_kernel_is_iso_of_image_eq_kernel _ _
      ((abelian.exact_iff_image_eq_kernel _ _).1 h) },
  { have hiso : is_iso ((category_theory.limits.image_subobject_iso f).hom ≫
      image_to_kernel' f g w) := by exactI is_iso.comp_is_iso,
    rw [image_subobject_iso_image_to_kernel'] at hiso,
    suffices : is_iso (image_to_kernel f g w),
    { haveI := this, apply_instance },
    exactI is_iso.of_is_iso_comp_right _ (kernel_subobject_iso g).hom }

end

lemma homology_is_zero_iff_image_to_kernel'_is_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  is_zero (homology f g w) ↔ is_iso (image_to_kernel' f g w) :=
⟨λ h, (exact_iff_image_to_kernel'_is_iso _ _ _).1 (exact_of_homology_is_zero h),
  λ h, exact.homology_is_zero _ _ ((exact_iff_image_to_kernel'_is_iso _ _ w).2 h)⟩

end
