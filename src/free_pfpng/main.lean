import free_pfpng.basic
import condensed.projective_resolution
import condensed.condensify
import condensed.adjunctions
import condensed.sheafification_mono

.


noncomputable theory

open category_theory
open opposite

-- jmc: This is maybe not the best way to set things up.
-- The counit in `free_pfpng_profinite_natural_map` will probably be annoying

universe u

def Profinite.condensed_free_pfpng (S : Profinite.{u}) : Condensed Ab :=
CompHausFiltPseuNormGrp.to_Condensed.obj $
  CompHausFiltPseuNormGrp₁.enlarging_functor.obj
  (ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng)

def Profinite.to_free_pfpng_level (S : Profinite.{u}) :
  S.to_Condensed ⟶ ((ProFiltPseuNormGrp₁.level.obj 1).obj S.free_pfpng).to_Condensed :=
Profinite_to_Condensed.map $ S.to_free_pfpng

def Profinite.to_condensed_free_pfpng (S : Profinite.{u}) :
  S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj S.condensed_free_pfpng :=
S.to_free_pfpng_level ≫
(CompHausFiltPseuNormGrp.level_Condensed_diagram_cocone
  (CompHausFiltPseuNormGrp₁.enlarging_functor.obj
  (ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng))).ι.app ⟨1⟩

@[simp]
lemma Profinite.to_condensed_free_pfpng_app (S T : Profinite.{u}) (f) :
  S.to_condensed_free_pfpng.val.app (op T) f = ulift.up
  ⟨_, 1, S.to_free_pfpng ∘ (ulift.down f).1,
    S.to_free_pfpng.2.comp (ulift.down f).2 ,rfl⟩ :=
rfl

def profinite_to_condensed_unit :
  Profinite_to_Condensed ⟶
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
  CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
  CompHausFiltPseuNormGrp.to_Condensed ⋙
  Condensed_Ab_to_CondensedSet :=
{ app := λ S, S.to_condensed_free_pfpng,
  naturality' := sorry }

def Profinite.free' (S : Profinite.{u}) : Condensed.{u} Ab.{u+1} :=
CondensedSet_to_Condensed_Ab'.obj S.to_Condensed

def Profinite.free'_lift (S : Profinite.{u}) {A : Condensed.{u} Ab.{u+1}}
  (η : S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj A) :
  S.free' ⟶ A :=
(Condensed_Ab_CondensedSet_adjunction'.hom_equiv _ _).symm η

def free'_lift {X : Type (u+1)} {A : Ab.{u+1}} (f : X → A) :
  AddCommGroup.free'.obj X ⟶ A :=
(AddCommGroup.adj'.hom_equiv _ _).symm f

open category_theory.grothendieck_topology

lemma Profinite.free'_lift_val_eq_sheafification_lift (S : Profinite.{u})
  {A : Condensed.{u} Ab.{u+1}}
  (η : S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj A)
  (T : Profinite.{u}) :
(S.free'_lift η).val.app (opposite.op T) =
  (sheafify_lift _ (((AddCommGroup.adj'.whiskering_right _).hom_equiv _ _).symm η.val)
    A.cond).app (opposite.op T) := rfl

def Profinite.free'_to_condensed_free_pfpng (S : Profinite.{u}) :
  S.free' ⟶ S.condensed_free_pfpng :=
S.free'_lift S.to_condensed_free_pfpng

instance Profinite.mono_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : mono S.free'_to_condensed_free_pfpng :=
begin
  apply presheaf_to_Condensed_Ab_map_mono_of_exists, intros B t ht,
  let e : S.to_Condensed.val.obj (op B) →
    S.condensed_free_pfpng.val.obj (op B) :=
    λ f, (S.to_condensed_free_pfpng.val.app (op B) f),
  dsimp at t ht,
  replace ht : free'_lift e t = 0,
  sorry { convert ht, ext u v, dsimp [free'_lift],
    simp only [adjunction.hom_equiv_counit, whiskering_right_obj_map,
      nat_trans.comp_app, whisker_right_app,
      adjunction.whisker_right_counit_app_app] },
  let ι : Π b : B, S.to_Condensed.val.obj (op B) → S :=
    λ b f, (ulift.down f).1 b,
  have aux : ∀ b : B, t.map_domain (ι b) = 0,
  { -- use discrete_quotient_separates_points'
    -- along with general stuff about bounded limits.
    sorry },
  -- At this point we need to carry out the inductive part of this proof...
  sorry
end

instance Profinite.epi_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : epi S.free'_to_condensed_free_pfpng := sorry

instance Profinite.is_iso_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : is_iso S.free'_to_condensed_free_pfpng :=
is_iso_of_mono_of_epi _

def Profinite.free_to_pfpng (S : Profinite.{u}) :
  CondensedSet_to_Condensed_Ab.obj S.to_Condensed ⟶
  S.condensed_free_pfpng :=
(Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _).symm S.to_condensed_free_pfpng

instance Profinite.is_iso_free_to_pfpng (S : Profinite.{u}) : is_iso S.free_to_pfpng :=
begin
  suffices : S.free_to_pfpng =
    (CondensedSet_to_Condensed_Ab_iso.app S.to_Condensed).hom ≫
    S.free'_to_condensed_free_pfpng,
  { rw this, apply_instance },
  sorry
end

def free_pfpng_profinite_natural_map :
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab ⟶
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
  CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
  CompHausFiltPseuNormGrp.to_Condensed :=
{ app := λ X, X.free_to_pfpng,
  naturality' := sorry }
/-
whisker_right profinite_to_condensed_unit _ ≫
(functor.associator _ _ _).hom ≫
whisker_left _ (
  (functor.associator _ _ _).hom ≫
  whisker_left _ (
    (functor.associator _ _ _).hom ≫
    whisker_left _ (
      (functor.associator _ _ _).hom ≫ whisker_left _
        Condensed_Ab_CondensedSet_adjunction.counit ≫ (functor.right_unitor _).hom )))
-/

/-
def profinite_to_condensed_unit :
  Profinite_to_Condensed ⟶
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) ⋙
    Condensed_Ab_to_CondensedSet :=
{ app := λ S, S.to_free_pfpng' ≫ _,
  naturality' := sorry }

def free_pfpng_profinite_natural_map :
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab ⟶
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) :=
(((whiskering_right _ _ _).obj CondensedSet_to_Condensed_Ab).map profinite_to_condensed_unit) ≫
  whisker_left
    (condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁))
    Condensed_Ab_CondensedSet_adjunction.counit
-/

instance free_pfpng_profinite_natural_map_is_iso :
  is_iso free_pfpng_profinite_natural_map :=
begin
  apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
  intros X,
  apply X.is_iso_free_to_pfpng,
end

/-- Prop 2.1 of Analytic.pdf -/
def free_pfpng_profinite_iso :
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) ≅
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab :=
sorry ≪≫ (as_iso free_pfpng_profinite_natural_map).symm

.

-- #check Condensed_Ab_CondensedSet_adjunction
