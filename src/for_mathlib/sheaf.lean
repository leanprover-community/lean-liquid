import category_theory.sites.sheaf

namespace category_theory.presheaf

open category_theory

variables {C : Type*} [category C] (J : grothendieck_topology C)
variables {D : Type*} [category D]

lemma is_sheaf_of_iso {F G : Cᵒᵖ ⥤ D} (η : F ≅ G) (hG : is_sheaf J G) : is_sheaf J F :=
begin
  intros T X S hS,
  let e : F ⋙ coyoneda.obj (opposite.op T) ≅ G ⋙ coyoneda.obj (opposite.op T) :=
    iso_whisker_right η _,
  apply presieve.is_sheaf_for_iso e.symm,
  apply hG _ _ hS,
end

end category_theory.presheaf
