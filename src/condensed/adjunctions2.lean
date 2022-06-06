import condensed.adjunctions
import condensed.top_comparison

noncomputable theory

universe u

open category_theory

namespace Sheaf

@[simps]
def hom_equiv {C D : Type*} [category C] [category D]
  {J : grothendieck_topology C} (F G : Sheaf J D) :
  (F ⟶ G) ≃ (F.val ⟶ G.val) :=
{ to_fun := λ f, f.val,
  inv_fun := λ f, ⟨f⟩,
  left_inv := λ f, by { cases f, refl },
  right_inv := λ f, rfl }

end Sheaf

namespace condensed


def profinite_free_adj_aux (M : Condensed.{u} Ab.{u+1}) (S : Profinite.{u}ᵒᵖ):
  (AddCommGroup.of ((CondensedSet_to_Condensed_Ab.obj (opposite.unop S).to_Condensed) ⟶ M)) ≃+
  (M.val.obj S) :=
let E := Condensed_Ab_CondensedSet_adjunction.hom_equiv S.unop.to_Condensed M,
  E' := E.trans (Sheaf.hom_equiv _ _),
  E'' := E'.trans (yoneda'_equiv _ _) in
{ map_add' := sorry,
  ..E'' }

def profinite_free_adj (M : Condensed.{u} Ab.{u+1}) :
  (Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab).op ⋙ preadditive_yoneda.obj M ≅
  M.val :=
nat_iso.of_components
(λ S, begin
  dsimp,
  apply add_equiv.to_AddCommGroup_iso,
  apply profinite_free_adj_aux,
end)
sorry

end condensed
