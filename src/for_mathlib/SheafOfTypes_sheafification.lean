import category_theory.sites.sheafification

namespace category_theory

open category_theory

universes v u
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)

noncomputable theory

def presheaf_to_SheafOfTypes : (Cᵒᵖ ⥤ Type (max v u)) ⥤ SheafOfTypes J :=
{ obj := λ P,
  { val := J.sheafify P,
    property := begin
      rw ← is_sheaf_iff_is_sheaf_of_type,
      exact grothendieck_topology.plus.is_sheaf_plus_plus J P,
    end },
  map := λ P Q η, (J.sheafification _).map η,
  map_id' := λ P, (J.sheafification _).map_id _,
  map_comp' := λ P Q R η γ, (J.sheafification _).map_comp _ _ }

-- Sanity check
def presheaf_to_SheafOfTypes_iso : presheaf_to_SheafOfTypes J ≅
  presheaf_to_Sheaf J _ ⋙ (Sheaf_equiv_SheafOfTypes J).functor := eq_to_iso rfl

-- The adjunction for sheaves of types
def sheafification_adjunction_types :
  (presheaf_to_SheafOfTypes J) ⊣ SheafOfTypes_to_presheaf J :=
show presheaf_to_Sheaf J _ ⋙ (Sheaf_equiv_SheafOfTypes J).functor ⊣
  (Sheaf_equiv_SheafOfTypes J).inverse ⋙ Sheaf_to_presheaf J _,
from adjunction.comp _ _ (sheafification_adjunction _ _) $
  (Sheaf_equiv_SheafOfTypes J).to_adjunction

instance is_iso_sheafification_types_adjunction_counit_app (X : SheafOfTypes J) :
  is_iso ((sheafification_adjunction_types J).counit.app X) :=
begin
  apply is_iso_of_reflects_iso _ (Sheaf_equiv_SheafOfTypes J).inverse,
  change is_iso ((sheafification_adjunction J (Type (max v u))).counit.app
    ((Sheaf_equiv_SheafOfTypes J).inverse.obj X)),
  apply_instance
end

instance sheafification_types_reflective : is_iso (sheafification_adjunction_types J).counit :=
nat_iso.is_iso_of_is_iso_app _

end category_theory
