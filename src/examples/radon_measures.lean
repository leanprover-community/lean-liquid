import examples.Radon.png
import challenge

/-!
In this file we will show that
-/

noncomputable theory

open_locale liquid_tensor_experiment nnreal zero_object
open liquid_tensor_experiment category_theory category_theory.limits

variables (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)]

example (S : Profinite.{0}) :
  (ℳ_{p} S) ≅
  CompHausFiltPseuNormGrp.to_Condensed.obj
  (CHFPNG₁_to_CHFPNGₑₗ.obj $ S.Radon_png p) :=
CompHausFiltPseuNormGrp.to_Condensed.map_iso $
CHFPNG₁_to_CHFPNGₑₗ.map_iso $ (S.Radon_png_iso p).symm
