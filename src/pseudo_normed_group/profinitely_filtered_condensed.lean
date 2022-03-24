import pseudo_normed_group.category.strictProFiltPseuNormGrpWithTinv
import laurent_measures.functor
import condensed.ab
import condensed.rescale
.

noncomputable theory

universe u

open_locale nnreal
open category_theory

variables {C : Type*} [category C] (r' : ℝ≥0) [fact (0 < r')]

abbreviation ProFiltPseuNormGrpWithTinv₁.to_CHFPNG₁ :
  ProFiltPseuNormGrpWithTinv₁.{u} r' ⥤ CompHausFiltPseuNormGrp₁.{u} :=
ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r' ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁

open ProFiltPseuNormGrpWithTinv₁ CompHausFiltPseuNormGrp₁ CompHausFiltPseuNormGrp

variables {r'}

def Tinv_nat_trans (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  F ⋙ to_CHFPNG₁.{u} r' ⋙ enlarging_functor ⟶
  F ⋙ to_CHFPNG₁.{u} r' ⋙ enlarging_functor :=
{ app := λ X, profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv,
  naturality' := λ X Y f, by { ext x, exact ((F.map f).map_Tinv x).symm } }

lemma Tinv_nat_trans_comp {F G : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'} (α : F ⟶ G) :
  Tinv_nat_trans F ≫ whisker_right α _ = whisker_right α _ ≫ Tinv_nat_trans G :=
by { ext X x, exact (α.app X).map_Tinv x }

def condensify (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
Profinite.extend.{u} F ⋙ to_CHFPNG₁.{u} r' ⋙ enlarging_functor.{u} ⋙ to_Condensed.{u}

def condensify_Tinv (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  condensify.{u} F ⟶ condensify.{u} F :=
@whisker_right _ _ _ _ _ _
  (Profinite.extend.{u} F ⋙ to_CHFPNG₁.{u} r' ⋙ enlarging_functor.{u})
  (Profinite.extend.{u} F ⋙ to_CHFPNG₁.{u} r' ⋙ enlarging_functor.{u})
  (Tinv_nat_trans (Profinite.extend F)) to_Condensed

variables {F G H : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'}

def condensify_map (α : F ⟶ G) : condensify F ⟶ condensify G :=
whisker_right (Profinite.extend_nat_trans α) _

lemma condensify_map_comp (α : F ⟶ G) (β : G ⟶ H) :
  condensify_map (α ≫ β) = condensify_map α ≫ condensify_map β :=
by simp only [condensify_map, Profinite.extend_nat_trans_comp, whisker_right_comp]

lemma condensify_map_comp_Tinv (α : F ⟶ G) :
  condensify_map α ≫ condensify_Tinv G = condensify_Tinv F ≫ condensify_map α :=
begin
  dsimp only [condensify_map, condensify_Tinv],
  simp only [← whisker_right_twice, ← whisker_right_comp],
  simp only [whisker_right_twice, Tinv_nat_trans_comp],
end
