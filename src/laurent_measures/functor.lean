import for_mathlib.Profinite.extend

import laurent_measures.basic
import pseudo_normed_group.category

noncomputable theory

universe u

open_locale nnreal

open category_theory

namespace laurent_measures

variables (r' : ℝ≥0) [fact (0 < r')]

open ProFiltPseuNormGrpWithTinv₁

@[simps] def fintype_functor : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' :=
{ obj := λ S, ⟨laurent_measures r' S, λ F, ⟨∥F∥₊, le_rfl⟩⟩,
  map := λ S T f, map_hom f,
  map_id' := λ S, by { ext1, simp only [map_hom, map_id], refl, },
  map_comp' := λ S S' S'' f g, by { ext1, simp only [map_hom, map_comp], refl } }

@[simps] def profinite : Profinite.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' :=
Profinite.extend (fintype_functor.{u} r')

instance (X : Profinite) : limits.preserves_limit X.diagram
  (profinite.{u} r' ⋙ to_CompHausFiltPseuNormGrp₁.{u u} r') :=
sorry

def profinite_comp_to_CompHausFiltPseuNormGrp₁ :
  laurent_measures.profinite.{u} r' ⋙ to_CompHausFiltPseuNormGrp₁.{u u} r' ≅
  Profinite.extend (fintype_functor.{u} r' ⋙ to_CompHausFiltPseuNormGrp₁.{u u} r') :=
(Profinite.extend_unique _ _ $
  (functor.associator _ _ _).symm.trans $
  iso_whisker_right (Profinite.extend_extends _) $ to_CompHausFiltPseuNormGrp₁.{u u} r')

end laurent_measures
