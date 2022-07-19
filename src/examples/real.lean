import challenge_notations
import challenge_prerequisites

/-!

This file shows that `ℝ` is a conditionally complete linearly ordered field.

-/

noncomputable theory

open_locale liquid_tensor_experiment nnreal zero_object
open liquid_tensor_experiment category_theory category_theory.limits opposite

example : conditionally_complete_linear_order ℝ := infer_instance
example : linear_ordered_field ℝ := infer_instance

example : ℝ≥0 = {r : ℝ // r ≥ 0} := rfl

-- TODO: once we bump mathlib past [#3292](https://github.com/leanprover-community/mathlib/pull/3292) we can show that `ℝ` is the unique
-- conditionally complete linearly ordered field, up to isomorphism.
