import category_theory.sites.dense_subsite

/-!
Content pulled from mathlib PR #14512
-/

universes w v v₁ v₂ v₃ u u₁ u₂ u₃
noncomputable theory
open category_theory
open opposite
open category_theory.presieve.family_of_elements
open category_theory.presieve
open category_theory.limits

variables {C D : Type u} [category.{v} C] [category.{v} D]
variables (A : Type w) [category.{max v u} A] [has_limits A]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}

variables
  [concrete_category.{max v u} A]
  [preserves_limits (forget A)]
  [reflects_isomorphisms (forget A)]
  [Π (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget A)]
  [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ A]
  [Π (X : D), preserves_colimits_of_shape (K.cover X)ᵒᵖ (forget A)]
  [∀ (X : D), has_colimits_of_shape (K.cover X)ᵒᵖ A]

namespace category_theory.sites

/-- The isomorphism exhibiting compatibility between pullback and sheafification. -/
def pullback_sheafification_compatibility
  {G : C ⥤ D} (Hp : cover_preserving J K G)
  (Hl : cover_lifting J K G) (Hc : compatible_preserving K G) :
  (whiskering_left _ _ A).obj G.op ⋙ presheaf_to_Sheaf J A ≅
  presheaf_to_Sheaf K A ⋙ sites.pullback A Hc Hp :=
let A1 : (whiskering_left _ _ A).obj G.op ⊣ _ := Ran.adjunction _ _,
    A2 : presheaf_to_Sheaf J A ⊣ _ := sheafification_adjunction _ _,
    B1 : presheaf_to_Sheaf K A ⊣ _ := sheafification_adjunction _ _,
    B2 : sites.pullback A Hc Hp ⊣ _ := sites.pullback_copullback_adjunction _ _ Hl _,
    A12 := A1.comp _ _ A2,
    B12 := B1.comp _ _ B2 in
A12.left_adjoint_uniq B12

lemma to_sheafify_pullback_sheafification_compatibility
  {G : C ⥤ D} (Hp : cover_preserving J K G)
  (Hl : cover_lifting J K G) (Hc : compatible_preserving K G) (F) :
  J.to_sheafify (G.op ⋙ F) ≫
  ((pullback_sheafification_compatibility.{w v u} A Hp Hl Hc).hom.app F).val =
  whisker_left _ (K.to_sheafify _) :=
begin
  dsimp [pullback_sheafification_compatibility, adjunction.left_adjoint_uniq],
  apply quiver.hom.op_inj,
  apply coyoneda.map_injective, swap, apply_instance,
  ext E f : 2,
  dsimp [functor.preimage, full.preimage, coyoneda, adjunction.left_adjoints_coyoneda_equiv],
  simp only [adjunction.hom_equiv_unit, functor.comp_map, Sheaf_to_presheaf_map,
    adjunction.hom_equiv_naturality_left_symm, whiskering_left_obj_map,
    adjunction.hom_equiv_counit, Sheaf.category_theory.category_comp_val,
    presheaf_to_Sheaf_map_val],
  dsimp [adjunction.comp],
  simp only [sheafification_adjunction_unit_app, category.comp_id, functor.map_id,
    whisker_left_id', category.assoc, grothendieck_topology.sheafify_map_sheafify_lift,
    category.id_comp, grothendieck_topology.to_sheafify_sheafify_lift],
  ext t,
  dsimp only [whisker_left, nat_trans.comp_app],
  simp only [category.assoc],
  -- for some reason the proof that works in mathllib does not work here...
  -- we have to be a little more forceful.
  erw [(Ran G.op).map_id, category.id_comp],
  congr' 1, simp only [← category.assoc],
  convert category.id_comp _,
  dsimp only [pullback_sheaf],
  have := (Ran.adjunction A G.op).left_triangle,
  apply_fun (λ e, (e.app (K.sheafify F)).app x) at this,
  exact this,
end

@[simp]
lemma pullback_sheafification_compatibility_hom_apply_val
  {G : C ⥤ D} (Hp : cover_preserving J K G)
  (Hl : cover_lifting J K G) (Hc : compatible_preserving K G) (F) :
((pullback_sheafification_compatibility.{w v u} A Hp Hl Hc).hom.app F).val =
  J.sheafify_lift (whisker_left _ $ K.to_sheafify _) (Sheaf.cond _) :=
begin
  apply J.sheafify_lift_unique,
  apply to_sheafify_pullback_sheafification_compatibility,
end

end category_theory.sites

namespace category_theory.cover_dense

variables {G : C ⥤ D} [full G] [faithful G]
variables (Hd : cover_dense K G) (Hp : cover_preserving J K G) (Hl : cover_lifting J K G)

/-- The isomorphism exhibiting the compatibiility of
`Sheaf_equiv_of_cover_preserving_cover_lifting` with sheafification. -/
noncomputable
abbreviation Sheaf_equiv_of_cover_preserving_cover_lifting_sheafification_compatibility :
  (whiskering_left _ _ A).obj G.op ⋙ presheaf_to_Sheaf _ _ ≅
  presheaf_to_Sheaf _ _ ⋙ (Sheaf_equiv_of_cover_preserving_cover_lifting Hd Hp Hl).inverse :=
category_theory.sites.pullback_sheafification_compatibility _ _ Hl _

end category_theory.cover_dense
