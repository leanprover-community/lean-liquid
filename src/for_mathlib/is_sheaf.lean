import category_theory.sites.sheaf

namespace category_theory.presheaf

open category_theory

variables {C D : Type*} [category C] [category D] (J : grothendieck_topology C)

lemma is_sheaf_iso (P Q : Cᵒᵖ ⥤ D) (E : Q ≅ P) :
  is_sheaf J P → is_sheaf J Q :=
begin
  intros h T X S hS,
  let e : (Q ⋙ coyoneda.obj (opposite.op T)) ≅
    (P ⋙ coyoneda.obj (opposite.op T)) := iso_whisker_right E _,
  apply presieve.is_sheaf_for_iso e.symm,
  apply h _ _ hS,
end

end category_theory.presheaf
