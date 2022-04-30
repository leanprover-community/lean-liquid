import challenge_notations
import for_mathlib.derived.les_facts
import laurent_measures.ses2
import laurent_measures.ext

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

open_locale liquid_tensor_experiment nnreal zero_object
open liquid_tensor_experiment category_theory category_theory.limits

variables (p' p : ℝ≥0) [fact (0 < p')] [fact (0 < (p : ℝ))]
variables [fact (p' < p)] [fact (p' ≤ 1)] [fact (p ≤ 1)]

set_option pp.universes true

-- move me
instance : fact (@r p < 1) :=
begin
  constructor, delta r,
  apply real.rpow_lt_one,
  { norm_num },
  { norm_num },
  { exact fact.out _ }
end

theorem liquid_tensor_experiment (S : Profinite.{1}) (V : pBanach.{1} p) :
  ∀ i > 0, Ext i (ℳ_{p'} S) V ≅ 0 :=
begin
  intros i hi,
  apply is_zero.iso_zero,
  revert i,
  haveI : fact (p' < 1) := ⟨lt_of_lt_of_le (fact.out _ : p' < p) (fact.out _)⟩,
  erw is_zero_iff_epi_and_is_iso _ _ (V : Condensed.{1 2 3} Ab) (laurent_measures.short_exact p' S),
  let := pBanach.choose_semi_normed_group V,
  let := pBanach.choose_normed_with_aut V (2⁻¹),
  haveI : fact (0 < (2⁻¹ : ℝ≥0) ^ (p : ℝ)) := r_pos',
  convert laurent_measures.epi_and_is_iso p' p S ⟨V⟩ _ using 1,
  intro v,
  rw [pBanach.choose_normed_with_aut_T_inv, inv_inv, two_smul, two_nsmul],
end
