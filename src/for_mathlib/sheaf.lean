import category_theory.sites.sheaf

namespace category_theory.presheaf

open category_theory

variables {C : Type*} [category C] (J : grothendieck_topology C)
variables {D : Type*} [category D]

lemma is_sheaf_of_iso {F G : Cᵒᵖ ⥤ D} (η : F ≅ G) (hG : is_sheaf J G) : is_sheaf J F :=
sorry

end category_theory.presheaf
