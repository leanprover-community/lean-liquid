import real_measures.basic
import condensed.ab
import for_mathlib.Profinite.extend

open_locale nnreal
open opposite category_theory

universe u

noncomputable theory

variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' ≤ 1)] [fact (p' < p)] [fact (p ≤ 1)]

def real_measures.profinite : Profinite.{u} ⥤ CompHausFiltPseuNormGrp₁.{u} :=
Profinite.extend (real_measures.functor p')

def real_measures.condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
real_measures.profinite p' ⋙ CompHausFiltPseuNormGrp₁.to_Condensed
