import banach
import real_measures
import condensed.projective_resolution
import category_theory.abelian.ext
import for_mathlib.Profinite.extend
import for_mathlib.abelian_category

open_locale nnreal
open opposite category_theory

noncomputable theory

variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' ≤ 1)] [fact (p' < p)] [fact (p ≤ 1)]

def real_measures.condensed : Profinite ⥤ Condensed Ab :=
Profinite.extend (real_measures.functor p') ⋙ CompHausFiltPseuNormGrp₁.to_Condensed

localized "notation `ℳ_{` p' `}` S := (real_measures.condensed p').obj S"
  in liquid_tensor_experiment

universe u

abbreviation liquid_tensor_experiment.Ext (i : ℕ) (A B : Condensed.{u} Ab.{u+1}) :=
((Ext ℤ (Condensed Ab) i).obj (op A)).obj B

instance : has_coe (pBanach p) (Condensed Ab) :=
{ coe := λ V, Condensed.of_top_ab V }
