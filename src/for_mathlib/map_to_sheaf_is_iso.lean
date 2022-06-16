import category_theory.sites.sheafification

open category_theory
open category_theory.limits
open opposite

namespace category_theory.Sheaf

universes w v u

-- All the classes we need for sheafification
variables
  {C : Type u} [category.{v} C]
  (J : grothendieck_topology C)
  {D : Type w} [category.{max v u} D] [concrete_category.{max v u} D]
  [preserves_limits (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
  [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
  [reflects_isomorphisms (forget D)]

lemma is_iso_of_eval {F : Sheaf J D} {G : Cᵒᵖ ⥤ D}
  (γ : F ⟶ (presheaf_to_Sheaf _ _).obj G)
  (η : F.val ⟶ G)
  [∀ X : C, is_iso (η.app (op X))]
  (h : γ.val = η ≫ J.to_sheafify _) :
  is_iso γ :=
begin
  haveI : is_iso (J.to_sheafify F.val) :=
    grothendieck_topology.is_iso_to_sheafify J F.2,
  have : γ.val = (J.to_sheafify F.val) ≫ (J.sheafify_map η),
  { rw ← is_iso.inv_comp_eq,
    apply J.sheafify_hom_ext, apply Sheaf.cond,
    rw [← grothendieck_topology.to_sheafify_naturality, ← h],
    simp },
  suffices : is_iso ((Sheaf_to_presheaf _ _).map γ),
  { resetI, apply is_iso_of_fully_faithful (Sheaf_to_presheaf J D) },
  dsimp, rw this,
  suffices : is_iso (J.sheafify_map η),
  { resetI, apply is_iso.comp_is_iso },
  change is_iso ((Sheaf_to_presheaf _ _).map ((presheaf_to_Sheaf _ _).map η)),
  haveI : is_iso η,
  { apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
    intros X, tactic.op_induction', apply_instance },
  apply_instance,
  apply_instance,
end

end category_theory.Sheaf
