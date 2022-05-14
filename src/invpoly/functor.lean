import for_mathlib.Profinite.extend

import invpoly.basic
import pseudo_normed_group.category

noncomputable theory

universe u

open_locale nnreal

open category_theory

open invpoly

variables (r : ℝ≥0) [fact (0 < r)] [fact (r < 1)]

open ProFiltPseuNormGrpWithTinv₁

/-- The functor represented by `ℤ[T⁻¹]`, i.e., sending a finite type `S` to the group
  `S → ℤ[T⁻¹]`, equipped with the filtration coming from the usual `r`-norm,
  i.e. the one sending `s ↦ ∑aₙ(s)T⁻ⁿ` to `∑_{s,n}∥aₙ(s)∥₊r⁻ⁿ`. We consider
  this object as a profinitely-filtered normed group equipped with an action of `T⁻¹`,
  given by multiplication. -/
@[simps] def Fintype_invpoly : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r :=
{ obj := λ S, ⟨invpoly r S, λ F, ⟨∥F∥₊, le_rfl⟩⟩,
  map := λ S T f, map_hom f,
  map_id' := λ S, by { ext1, simp only [map_hom, map_id], refl, },
  map_comp' := λ S S' S'' f g, by { ext1, simp only [map_hom, map_comp], refl } }
