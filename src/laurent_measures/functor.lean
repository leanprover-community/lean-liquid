import for_mathlib.Profinite.extend

import laurent_measures.basic
import pseudo_normed_group.category

noncomputable theory

open_locale nnreal

open category_theory

namespace laurent_measures

variables (r' : ℝ≥0) [fact (0 < r')]

@[simps] def fintype_functor : Fintype ⥤ ProFiltPseuNormGrpWithTinv₁ r' :=
{ obj := λ S, ⟨laurent_measures r' S, λ F, ⟨∥F∥₊, le_rfl⟩⟩,
  map := λ S T f, map_hom f,
  map_id' := λ S, by { ext1, simp only [map_hom, map_id], refl, },
  map_comp' := λ S S' S'' f g, by { ext1, simp only [map_hom, map_comp], refl } }

@[simps] def functor : Profinite ⥤ ProFiltPseuNormGrpWithTinv₁ r' :=
Profinite.extend (fintype_functor r')

end laurent_measures
