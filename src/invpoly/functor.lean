import for_mathlib.Profinite.extend

import invpoly.basic
import pseudo_normed_group.category

noncomputable theory

universe u

open_locale nnreal

open category_theory

namespace invpoly

variables (r' : ℝ≥0) [fact (0 < r')]

open ProFiltPseuNormGrpWithTinv₁

@[simps] def fintype_functor : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' :=
{ obj := λ S, ⟨invpoly r' S, λ F, ⟨∥F∥₊, le_rfl⟩⟩,
  map := λ S T f, map_hom f,
  map_id' := λ S, by { ext1, simp only [map_hom, map_id], refl, },
  map_comp' := λ S S' S'' f g, by { ext1, simp only [map_hom, map_comp], refl } }

-- @[simps] def profinite : Profinite.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' :=
-- Profinite.extend (fintype_functor.{u} r')

-- @[simps] def profiniteCH : Profinite.{u} ⥤ CompHausFiltPseuNormGrp₁.{u} :=
-- Profinite.extend (fintype_functor.{u} r' ⋙ to_CompHausFiltPseuNormGrp₁.{u} r')

-- def profinite_comp_to_CompHausFiltPseuNormGrp₁ :
--   invpoly.profinite.{u} r' ⋙ to_CompHausFiltPseuNormGrp₁.{u} r' ≅
--   profiniteCH.{u} r' :=
-- Profinite.extend_commutes _ _

end invpoly
