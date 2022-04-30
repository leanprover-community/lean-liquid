import for_mathlib.Profinite.extend

import laurent_measures.basic
import pseudo_normed_group.category

noncomputable theory

universe u

open_locale nnreal

open category_theory

section Laurent_measures_def

open laurent_measures

def Fintype.Laurent_measures (r : ℝ≥0) [fact (0 < r)] (S : Fintype.{u}) :
  ProFiltPseuNormGrpWithTinv₁.{u} r :=
⟨laurent_measures r S, λ F, ⟨∥F∥₊, le_rfl⟩⟩

/-- `Laurent_measures r'` is an explicit functor from finite types to the category of profinitely
  exhaustively-filtered pseudo-normed groups with an action of T⁻¹, and strict morphisms. It sends
  `S` to the Laurent measures on `S` with bound `r'`. -/
@[simps] def Fintype_Laurent_measures (r : ℝ≥0) [fact (0 < r)] :
  Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r :=
{ obj := λ S, ⟨laurent_measures r S, λ F, ⟨∥F∥₊, le_rfl⟩⟩,
  map := λ S T f, map_hom f,
  map_id' := λ S, by { ext1, simp only [map_hom, map_id], refl, },
  map_comp' := λ S S' S'' f g, by { ext1, simp only [map_hom, map_comp], refl } }

end Laurent_measures_def

namespace laurent_measures

variables (r' : ℝ≥0) [fact (0 < r')]

open ProFiltPseuNormGrpWithTinv₁

@[simps] def profinite : Profinite.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' :=
Profinite.extend (Fintype_Laurent_measures.{u} r')

@[simps] def profiniteCH : Profinite.{u} ⥤ CompHausFiltPseuNormGrp₁.{u} :=
Profinite.extend (Fintype_Laurent_measures.{u} r' ⋙ to_CompHausFiltPseuNormGrp₁.{u} r')

def profinite_comp_to_CompHausFiltPseuNormGrp₁ :
  laurent_measures.profinite.{u} r' ⋙ to_CompHausFiltPseuNormGrp₁.{u} r' ≅
  profiniteCH.{u} r' :=
Profinite.extend_commutes _ _

end laurent_measures
