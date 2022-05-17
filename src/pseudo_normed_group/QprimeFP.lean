import pseudo_normed_group.FP2
import condensed.adjunctions
import free_pfpng.acyclic

noncomputable theory

open_locale nnreal

universe u

open category_theory breen_deligne

variables (r' : ℝ≥0)
variables (BD : breen_deligne.data) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r')

abbreviation freeCond := Profinite_to_Condensed.{u} ⋙ CondensedSet_to_Condensed_Ab

def QprimeFP : ℝ≥0 ⥤ chain_complex (Condensed.{u} Ab.{u+1}) ℕ :=
FPsystem r' BD M κ ⋙ (freeCond.{u}.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _

-- variables (f : ℕ → ℝ≥0)
-- #check ∐ (λ i, (QprimeFP r' BD κ M).obj (f i))
