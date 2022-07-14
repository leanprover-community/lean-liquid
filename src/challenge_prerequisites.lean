import challenge_notations
import for_mathlib.derived.les_facts
import laurent_measures.ses2
import laurent_measures.ext


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
