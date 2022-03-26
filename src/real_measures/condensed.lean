import real_measures.basic
import condensed.ab
import for_mathlib.Profinite.extend
import condensed.condensify

open_locale nnreal
open opposite category_theory

universe u

noncomputable theory

variables (p' : ℝ≥0) [fact (0 < p')] [fact (p' ≤ 1)]

def real_measures.condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
condensify (real_measures.functor p')
