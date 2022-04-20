import free_pfpng.basic
import condensed.projective_resolution
import condensed.condensify
import condensed.adjunctions
.

noncomputable theory

open category_theory

-- jmc: This is maybe not the best way to set things up.
-- The counit in `free_pfpng_profinite_natural_map` will probably be annoying

universe u

def Profinite.free_pfpng' (S : Profinite.{u}) : Condensed Ab :=
CompHausFiltPseuNormGrp.to_Condensed.obj $
  CompHausFiltPseuNormGrp₁.enlarging_functor.obj
  (ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng)

def Profinite.to_free_pfpng'_level (S : Profinite.{u}) :
  S.to_Condensed ⟶ ((ProFiltPseuNormGrp₁.level.obj 1).obj S.free_pfpng).to_Condensed :=
Profinite_to_Condensed.map $ S.to_free_pfpng

def Profinite.to_free_pfpng' (S : Profinite.{u}) :
  S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj S.free_pfpng' :=
S.to_free_pfpng'_level ≫
(CompHausFiltPseuNormGrp.level_Condensed_diagram_cocone
  (CompHausFiltPseuNormGrp₁.enlarging_functor.obj
  (ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng))).ι.app ⟨1⟩

def profinite_to_condensed_unit :
  Profinite_to_Condensed ⟶
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
  CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
  CompHausFiltPseuNormGrp.to_Condensed ⋙
  Condensed_Ab_to_CondensedSet :=
{ app := λ S, S.to_free_pfpng',
  naturality' := sorry }

def Profinite.free'_to_pfpng (S : Profinite.{u}) :
  CondensedSet_to_Condensed_Ab'.obj S.to_Condensed ⟶
  CompHausFiltPseuNormGrp.to_Condensed.obj
  (CompHausFiltPseuNormGrp₁.enlarging_functor.obj
  (ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng)) :=
(Condensed_Ab_CondensedSet_adjunction'.hom_equiv _ _).symm S.to_free_pfpng'

instance Profinite.is_iso_free'_to_pfpng (S : Profinite.{u}) : is_iso S.free'_to_pfpng := sorry

def Profinite.free_to_pfpng (S : Profinite.{u}) :
  CondensedSet_to_Condensed_Ab.obj S.to_Condensed ⟶
  CompHausFiltPseuNormGrp.to_Condensed.obj
  (CompHausFiltPseuNormGrp₁.enlarging_functor.obj
  (ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng)) :=
(Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _).symm S.to_free_pfpng'

instance Profinite.is_iso_free_to_pfpng (S : Profinite.{u}) : is_iso S.free_to_pfpng :=
begin
  suffices : S.free_to_pfpng =
    (CondensedSet_to_Condensed_Ab_iso.app S.to_Condensed).hom ≫
    S.free'_to_pfpng,
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
