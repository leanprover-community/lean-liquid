import system_of_complexes.complex

import category_theory.preadditive.additive_functor

namespace differential_object

namespace complex_like

open category_theory category_theory.limits

variables {ι : Type} {V₁ V₂ : Type*} {cov : bool}
variables [has_succ ι] [category V₁] [category V₂] [preadditive V₁] [preadditive V₂]

-- this is of course functorial in `C`
def modify (C : complex_like ι V₁ cov) (F : ι → V₁ ⥤ V₂) (α : Π i j, F i ⟶ F j)
  [Π i, (F i).additive] :
  complex_like ι V₂ cov :=
{ X := λ i, (F i).obj (C.X i),
  d := λ i j, (F i).map (C.d i j) ≫ (α i j).app _,
  d_comp_d := λ i j k,
  by simp only [nat_trans.naturality_assoc, ← functor.map_comp_assoc, category.assoc, C.d_comp_d,
      category_theory.functor.map_zero, zero_comp, comp_zero],
  d_eq_zero := λ i j h, by rw [C.d_eq_zero h, category_theory.functor.map_zero, zero_comp] }

end complex_like

end differential_object
