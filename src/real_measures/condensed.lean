import real_measures.basic
import condensed.ab
import for_mathlib.Profinite.extend

open_locale nnreal
open opposite category_theory

noncomputable theory

variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' ≤ 1)] [fact (p' < p)] [fact (p ≤ 1)]

def real_measures.condensed : Profinite ⥤ Condensed Ab :=
Profinite.extend (real_measures.functor p') ⋙ CompHausFiltPseuNormGrp₁.to_Condensed
