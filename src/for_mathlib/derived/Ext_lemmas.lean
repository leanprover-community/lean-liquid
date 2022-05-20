import for_mathlib.derived.derived_cat
import for_mathlib.derived.example
import for_mathlib.short_exact

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

def Ext'_zero_flip_iso (B : A) :
  (Ext' 0).flip.obj B ≅ (preadditive_yoneda.obj B) :=
sorry

end bounded_derived_category
