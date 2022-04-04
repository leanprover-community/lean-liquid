import for_mathlib.derived.derived_cat

open category_theory
open category_theory.triangulated
variables (A : Type*) [category A] [abelian A] [enough_projectives A]

namespace bounded_derived_category

@[simps]
def forget : bounded_derived_category A ⥤ bounded_homotopy_category A :=
{ obj := λ X, X.val,
  map := λ _ _ f, f.val,
  map_id' := λ _ , rfl,
  map_comp' := λ _ _ _ _ _, rfl }

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

end bounded_derived_category
