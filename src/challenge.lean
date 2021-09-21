import banach
import real_measures
import condensed.ab
import category_theory.abelian.ext
import for_mathlib.Profinite.extend
import for_mathlib.abelian_category

/-!
# Liquid Tensor Experiment

## The main challenge

The main challenge of the liquid tensor experiment is
a formalisation of the first theorem in Peter Scholze's blogpost
https://xenaproject.wordpress.com/2020/12/05/liquid-tensor-experiment/

Theorem 1.1 (Clausen--Scholze)
Let `0 < p' < p ≤ 1` be real numbers, let `S` be a profinite set, and let `V` be a `p`-Banach space.
Let `ℳ p' S` be the space of `p'`-measures on `S`. Then
$$ Ext^i (ℳ p' S, V) = 0 $$
for `i ≥ 1`.

-/

noncomputable theory

open_locale nnreal
open opposite category_theory

variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' ≤ 1)] [fact (p' < p)] [fact (p ≤ 1)]
variables (S : Profinite.{1})
variables (V : Type 1) [normed_group V] [module ℝ V] [normed_space' ℝ p V] -- `V` is a `p`-Banach

def real_measures.condensed : Profinite ⥤ Condensed Ab :=
Profinite.extend (real_measures.functor p') ⋙ CompHausFiltPseuNormGrp₁.to_Condensed

local notation `ℳ` p' := real_measures.condensed p'

local notation `Ext` i `,` A `,` B := ((Ext ℤ (Condensed Ab) i).obj (op A)).obj B

theorem main_challenge (i : ℕ) (hi : 0 < i) :
  is_zero (Ext i , (ℳ p').obj S , Condensed.of_top_ab V) :=
sorry