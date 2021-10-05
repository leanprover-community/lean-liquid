import challenge_notations

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

open_locale nnreal liquid_tensor_experiment
open liquid_tensor_experiment

variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' ≤ 1)] [fact (p' < p)] [fact (p ≤ 1)]
variables (S : Profinite.{1}) (V : pBanach p)

theorem liquid_tensor_experiment (i : ℕ) (hi : 0 < i) :
  Ext i (ℳ_{p'} S) V ≅ 0 :=
sorry
