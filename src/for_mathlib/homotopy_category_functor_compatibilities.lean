import for_mathlib.homotopy_category_op

noncomputable theory

open opposite

namespace category_theory

namespace functor

def quotient_op_map_homology_nat_iso {A B : Type*}
  [category A] [category B] [abelian A] [abelian B] (F : Aᵒᵖ ⥤ B)
  {ι : Type*} (c : complex_shape ι)
  [functor.additive F] (i : ι) :
  (homotopy_category.quotient A c).op ⋙ homotopy_category.op_functor ⋙
    functor.map_homotopy_category c.symm F ⋙ homotopy_category.homology_functor _ _ i ≅
    homological_complex.op_functor ⋙ F.map_homological_complex c.symm ⋙
  homology_functor _ _ i :=
begin
  refine _ ≪≫
    iso_whisker_left (homological_complex.op_functor ⋙ F.map_homological_complex c.symm)
    (homotopy_category.homology_factors B c.symm i) ≪≫ functor.associator _ _ _,
  refine functor.associator _ _ _ ≪≫ _ ≪≫ (functor.associator _ _ _).symm,
  refine iso_whisker_left _ _,
  refine (functor.associator _ _ _).symm ≪≫ _ ≪≫ functor.associator _ _ _,
  refine iso_whisker_right _ _,
  exact (F.map_homotopy_category_comp c.symm).symm,
end

def quotient_op_map_homology_iso {A B : Type*}
  [category A] [category B] [abelian A] [abelian B] (F : Aᵒᵖ ⥤ B)
  {ι : Type*} {c : complex_shape ι}
  [functor.additive F] (X : homotopy_category A c) (i : ι) :
  (homotopy_category.op_functor ⋙
    functor.map_homotopy_category c.symm F ⋙
    homotopy_category.homology_functor _ _ i).obj (op X) ≅
  (F.map_homological_complex c.symm ⋙ homology_functor _ _ i).obj X.as.op :=
begin
  have e : op X ≅ (homotopy_category.quotient A c).op.obj (op X.as),
  { dsimp,
    apply iso.op,
    apply eq_to_iso,
    cases X,
    refl, },
  refine _ ≪≫ (F.quotient_op_map_homology_nat_iso c i).app (op X.as) ≪≫ _,
  { exact (homotopy_category.op_functor ⋙ functor.map_homotopy_category c.symm F ⋙
     homotopy_category.homology_functor B c.symm i).map_iso e, },
  { refl, },
end

end functor

end category_theory
