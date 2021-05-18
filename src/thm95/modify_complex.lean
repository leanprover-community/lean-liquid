import algebra.homology.homological_complex
import category_theory.preadditive.additive_functor

namespace homological_complex

open category_theory category_theory.limits

variables {ι : Type} {V₁ V₂ : Type*} {c : complex_shape ι}
variables [category V₁] [category V₂] [preadditive V₁] [preadditive V₂]

-- this is of course functorial in `C`
def modify (C : homological_complex V₁ c) (F : ι → V₁ ⥤ V₂) (α : Π i j, F i ⟶ F j)
  [Π i, (F i).additive] :
  homological_complex V₂ c :=
{ X := λ i, (F i).obj (C.X i),
  d := λ i j, (F i).map (C.d i j) ≫ (α i j).app _,
  d_comp_d' := λ i j k,
  by simp only [nat_trans.naturality_assoc, ← functor.map_comp_assoc, category.assoc, C.d_comp_d,
      category_theory.functor.map_zero, zero_comp, comp_zero],
  shape' := λ i j h, by rw [C.shape _ _ h, category_theory.functor.map_zero, zero_comp] }


end homological_complex
