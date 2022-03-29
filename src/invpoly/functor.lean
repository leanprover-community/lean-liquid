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

end invpoly
