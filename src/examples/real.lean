import challenge_notations
import challenge_prerequisites

import algebra.order.complete_field

/-!

This file shows that `ℝ` is a conditionally complete linearly ordered field.

Key result from mathlib:
[#3292](https://github.com/leanprover-community/mathlib/pull/3292)

-/

noncomputable theory

open_locale liquid_tensor_experiment nnreal zero_object
open liquid_tensor_experiment category_theory category_theory.limits opposite

example : conditionally_complete_linear_order ℝ := infer_instance
example : linear_ordered_field ℝ := infer_instance

example : ℝ≥0 = {r : ℝ // r ≥ 0} := rfl

-- Any conditionally complete linear ordered field is isomorphic (as an ordered ring) to `ℝ`.
example {R : Type*} [conditionally_complete_linear_ordered_field R] : R ≃+*o ℝ := default

-- The isomorphism above is unique
example {R : Type*} [conditionally_complete_linear_ordered_field R] (e₁ e₂ : R ≃+*o ℝ) :
  e₁ = e₂ := subsingleton.elim _ _
