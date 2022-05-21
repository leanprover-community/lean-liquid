import for_mathlib.derived.derived_cat
import for_mathlib.derived.example
import for_mathlib.derived.les_facts
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

-- move me
lemma Ext'_zero_left_is_zero {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  (A : 𝓐ᵒᵖ) (B : 𝓐) (hA : is_zero A) (i : ℤ) :
  is_zero (((Ext' i).obj A).obj B) :=
begin
  rw is_zero_iff_id_eq_zero at hA ⊢,
  rw [← functor.flip_obj_obj, ← category_theory.functor.map_id, hA, functor.map_zero],
end

end bounded_derived_category
