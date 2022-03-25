import pseudo_normed_group.category.strictProFiltPseuNormGrpWithTinv
import laurent_measures.functor
import condensed.ab
import condensed.rescale
.

noncomputable theory

universe u

open_locale nnreal
open category_theory

variables {C D : Type*} [category C] [category D] (r' : ℝ≥0) [fact (0 < r')]

abbreviation category_theory.nat_trans.conj_by {F G : C ⥤ D} (α : F ≅ G) (β : G ⟶ G) :
  F ⟶ F := α.hom ≫ β ≫ α.inv

open category_theory

abbreviation ProFiltPseuNormGrpWithTinv₁.to_CHFPNG₁ :
  ProFiltPseuNormGrpWithTinv₁.{u} r' ⥤ CompHausFiltPseuNormGrp₁.{u} :=
ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r' ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁

open ProFiltPseuNormGrpWithTinv₁ CompHausFiltPseuNormGrp₁ CompHausFiltPseuNormGrp

variables {r'}

def condensify (F : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
Profinite.extend.{u} F ⋙ enlarging_functor.{u} ⋙ to_Condensed.{u}

variables {F G H : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}}

def condensify_map (α : F ⟶ G) : condensify F ⟶ condensify G :=
whisker_right (Profinite.extend_nat_trans α) _

lemma condensify_map_comp (α : F ⟶ G) (β : G ⟶ H) :
  condensify_map (α ≫ β) = condensify_map α ≫ condensify_map β :=
by simp only [condensify_map, Profinite.extend_nat_trans_comp, whisker_right_comp]

def condensify_def (F : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  condensify F ≅ Profinite.extend.{u} F ⋙ enlarging_functor.{u} ⋙ to_Condensed.{u} :=
iso.refl _

def Tinv_nat_trans (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  F ⋙ to_CHFPNG₁.{u} r' ⋙ enlarging_functor ⟶
  F ⋙ to_CHFPNG₁.{u} r' ⋙ enlarging_functor :=
{ app := λ X, profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv,
  naturality' := λ X Y f, by { ext x, exact ((F.map f).map_Tinv x).symm } }

lemma Tinv_nat_trans_comp {F G : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'} (α : F ⟶ G) :
  Tinv_nat_trans F ≫ whisker_right α _ = whisker_right α _ ≫ Tinv_nat_trans G :=
by { ext X x, exact (α.app X).map_Tinv x }

def condensify_Tinv (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  condensify.{u} (F ⋙ to_CHFPNG₁ r') ⟶ condensify.{u} (F ⋙ to_CHFPNG₁ r') :=
nat_trans.conj_by (functor.associator _ _ _).symm $
  whisker_right (nat_trans.conj_by
    (iso_whisker_right (Profinite.extend_commutes _ _).symm enlarging_functor.{u}) $
      Tinv_nat_trans.{u} (Profinite.extend.{u} F)) _

lemma condensify_map_comp_Tinv {F G : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'}
  (α : F ⟶ G) :
  condensify_map (whisker_right α (to_CHFPNG₁ r')) ≫ condensify_Tinv G =
  condensify_Tinv F ≫ condensify_map (whisker_right α (to_CHFPNG₁ r')) :=
begin
  delta condensify_map condensify_Tinv nat_trans.conj_by,
  ext X : 2,
  simp only [iso.symm_hom, iso_whisker_right_hom, iso_whisker_right_inv, iso.symm_inv,
    whisker_right_comp, whisker_right_twice, category.assoc],
  simp only [nat_trans.comp_app, functor.associator_hom_app, functor.associator_inv_app],
  erw [category.id_comp, category.id_comp, category.comp_id, category.id_comp],
  simp only [← nat_trans.comp_app, ← whisker_right_twice, ← whisker_right_comp],
  congr' 2,
  simp only [← iso_whisker_right_hom, ← iso_whisker_right_inv, iso.eq_inv_comp],
  simp only [iso_whisker_right_hom, iso_whisker_right_inv, ← whisker_right_comp_assoc],
  sorry
  -- have := Tinv_nat_trans_comp (Profinite.extend_nat_trans α),
  -- rw [← Profinite.extend_nat_trans_whisker_right],
  -- -- erw [← whisker_right_comp_assoc],
  -- simp only [whisker_right_twice, Tinv_nat_trans_comp],
end
