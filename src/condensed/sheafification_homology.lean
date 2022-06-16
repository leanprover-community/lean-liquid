import condensed.exact

namespace Condensed

universe u

noncomputable
abbreviation homology_functor_sheafification_iso
  {M : Type*} (c : complex_shape M) (i : M) :
  homology_functor (Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) c i ⋙ presheaf_to_Condensed_Ab ≅
  presheaf_to_Condensed_Ab.map_homological_complex _ ⋙ homology_functor _ c i :=
category_theory.functor.homology_functor_iso _ _ _

end Condensed
