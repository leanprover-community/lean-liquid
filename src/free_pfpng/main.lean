import free_pfpng.epi
import free_pfpng.mono

noncomputable theory

open_locale classical big_operators

open category_theory
open opposite
open category_theory.grothendieck_topology

universe u

lemma Profinite.is_zero_of_empty (S : Profinite.{u}) [is_empty S] :
  limits.is_zero S.condensed_free_pfpng := sorry

lemma category_theory.abelian.is_iso_of_mono_of_is_zero
  {A : Type*} [category A] [abelian A] {X Y : A} (f : X ⟶ Y) [mono f]
  (hY : limits.is_zero Y) : is_iso f :=
begin
  use 0, simp, split,
  rw ← cancel_mono f,
  apply hY.eq_of_tgt,
  apply hY.eq_of_tgt,
end

instance Profinite.epi_free'_to_condensed_free_pfpng_of_empty
  (S : Profinite.{u}) [is_empty S] :
  epi S.free'_to_condensed_free_pfpng :=
begin
  suffices : is_iso S.free'_to_condensed_free_pfpng,
  { resetI, apply_instance },
  apply category_theory.abelian.is_iso_of_mono_of_is_zero,
  apply Profinite.is_zero_of_empty,
end

-- Do a case split on `[nonempty S]` here.
instance Profinite.epi_free'_to_condensed_free_pfpng (S : Profinite.{u}) :
  epi S.free'_to_condensed_free_pfpng :=
begin
  by_cases hS : nonempty S, { resetI, apply_instance },
  simp only [not_nonempty_iff] at hS,
  resetI, apply_instance
end

instance Profinite.is_iso_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : is_iso S.free'_to_condensed_free_pfpng :=
is_iso_of_mono_of_epi _

def Profinite.free_to_pfpng (S : Profinite.{u}) :
  CondensedSet_to_Condensed_Ab.obj S.to_Condensed ⟶
  S.condensed_free_pfpng :=
(Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _).symm S.to_condensed_free_pfpng

attribute [simps hom_app] AddCommGroup.free_iso_free'

instance Profinite.is_iso_free_to_pfpng (S : Profinite.{u}) : is_iso S.free_to_pfpng :=
begin
  suffices : S.free_to_pfpng =
    (CondensedSet_to_Condensed_Ab_iso.app S.to_Condensed).hom ≫
    S.free'_to_condensed_free_pfpng,
  { rw this, apply_instance },
  rw [iso.app_hom],
  delta Profinite.free'_to_condensed_free_pfpng Profinite.free'_lift Profinite.free_to_pfpng
    CondensedSet_to_Condensed_Ab_iso Sheaf.adjunction
    Condensed_Ab_CondensedSet_adjunction Condensed_Ab_CondensedSet_adjunction',
  ext T : 4,
  dsimp only [adjunction.mk_of_hom_equiv_hom_equiv, functor.map_iso_hom, quiver.hom.forget_Ab,
    Sheaf.hom.comp_val, Condensed_Ab_to_CondensedSet_map, Sheaf.compose_equiv_symm_apply_val,
    presheaf_to_Sheaf_map_val, nat_trans.comp_app,
    iso_whisker_left_hom, iso_whisker_right_hom, whisker_left_app, whisker_right_app],
  rw [← nat_trans.comp_app, sheafify_map_sheafify_lift],
  congr' 4, clear T,
  ext T : 2,
  dsimp only [whiskering_right_map_app_app, whiskering_right_obj_map, nat_trans.comp_app,
    adjunction.whisker_right, adjunction.mk_of_unit_counit_hom_equiv_symm_apply,
    whisker_left_app, whisker_right_app,
    functor.associator_hom_app, functor.right_unitor_hom_app],
  erw [category.id_comp, category.id_comp, category.comp_id, category.comp_id],
  rw [← nat_trans.naturality_assoc],
  congr' 1,
  dsimp only [AddCommGroup.adj, AddCommGroup.adj', adjunction.mk_of_hom_equiv_hom_equiv,
    adjunction.of_nat_iso_left, adjunction.mk_of_hom_equiv_counit_app,
    equiv.inv_fun_as_coe, equiv.symm_trans_apply, iso.symm_hom,
    adjunction.equiv_homset_left_of_nat_iso_symm_apply],
  simp only [equiv.symm_symm],
  erw [← category.assoc, ← nat_trans.comp_app, iso.hom_inv_id, nat_trans.id_app,
    category.id_comp],
end

def free_pfpng_profinite_natural_map :
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab ⟶
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
  CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
  CompHausFiltPseuNormGrp.to_Condensed :=
{ app := λ X, X.free_to_pfpng,
  naturality' := λ S T f, begin
    -- we should be able to precompose with the natural map `S.to_Condensed ⟶ S.free'`
    -- how do we do that?
    sorry
  end }
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
