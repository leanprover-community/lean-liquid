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

variables (M : Condensed.{u} Ab.{u+1}) (S T : Profinite.{u}ᵒᵖ) (f : S ⟶ T)

def profinite_free_adj_aux₁  :
  (CondensedSet_to_Condensed_Ab.obj (opposite.unop S).to_Condensed ⟶ M) ≃
  ((opposite.unop S).to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj M) :=
Condensed_Ab_CondensedSet_adjunction.hom_equiv S.unop.to_Condensed M

lemma profinite_free_adj_aux₁_naturality
  (x : CondensedSet_to_Condensed_Ab.obj S.unop.to_Condensed ⟶ M) :
  profinite_free_adj_aux₁ _ _
  ((CondensedSet_to_Condensed_Ab.map (Profinite_to_Condensed.map f.unop) ≫ x)) =
  Profinite_to_Condensed.map f.unop ≫ profinite_free_adj_aux₁ _ _ x :=
begin
  dsimp only [profinite_free_adj_aux₁],
  simpa only [adjunction.hom_equiv_naturality_left],
end

def profinite_free_adj_aux₂ (M : Condensed.{u} Ab.{u+1}) (S : Profinite.{u}ᵒᵖ) :
  ((opposite.unop S).to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj M) ≃
  ((opposite.unop S).to_Condensed.val ⟶ (Condensed_Ab_to_CondensedSet.obj M).val) :=
(Sheaf.hom_equiv _ _)

lemma profinite_free_adj_aux₂_naturality
  (x : S.unop.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj M) :
  profinite_free_adj_aux₂ _ _ ((Profinite_to_Condensed.map f.unop) ≫ x) =
  (Profinite_to_Condensed.map f.unop).val ≫ profinite_free_adj_aux₂ _ _ x := rfl

def profinite_free_adj_aux₃ (M : Condensed.{u} Ab.{u+1}) (S : Profinite.{u}ᵒᵖ) :
  ((opposite.unop S).to_Condensed.val ⟶ (Condensed_Ab_to_CondensedSet.obj M).val) ≃
  (M.val.obj S) :=
yoneda'_equiv _ _

lemma profinite_free_adj_aux₃_naturality
  (x : (opposite.unop S).to_Condensed.val ⟶ (Condensed_Ab_to_CondensedSet.obj M).val) :
  profinite_free_adj_aux₃ _ _ ((Profinite_to_Condensed.map f.unop).val ≫ x) =
  (M.val.map f) (profinite_free_adj_aux₃ _ _ x) :=
begin
  have := x.naturality f,
  apply_fun (λ e, e (ulift.up (𝟙 S.unop))) at this,
  exact this,
end

def profinite_free_adj_aux (M : Condensed.{u} Ab.{u+1}) (S : Profinite.{u}ᵒᵖ):
  (AddCommGroup.of ((CondensedSet_to_Condensed_Ab.obj (opposite.unop S).to_Condensed) ⟶ M)) ≃+
  (M.val.obj S) :=
{ map_add' := λ f g, rfl,
  ..((profinite_free_adj_aux₁ M S).trans
    ((profinite_free_adj_aux₂ _ _).trans
    (profinite_free_adj_aux₃ _ _))) }

def profinite_free_adj (M : Condensed.{u} Ab.{u+1}) :
  (Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab).op ⋙ preadditive_yoneda.obj M ≅
  M.val :=
nat_iso.of_components
(λ S, begin
  apply add_equiv.to_AddCommGroup_iso,
  apply profinite_free_adj_aux,
end)
begin
  intros S T f, ext t,
  change ((profinite_free_adj_aux₁ M T).trans
    ((profinite_free_adj_aux₂ M T).trans (profinite_free_adj_aux₃ M T))) _ = _,
  dsimp only [equiv.trans_apply, functor.comp_map, functor.op_map, preadditive_yoneda],
  erw profinite_free_adj_aux₁_naturality,
  erw profinite_free_adj_aux₂_naturality,
  erw profinite_free_adj_aux₃_naturality,
  refl,
end

end condensed
