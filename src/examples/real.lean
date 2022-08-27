import challenge_notations
import challenge_prerequisites

import algebra.order.complete_field -- the theory of complete linearly ordered fields.

/-!

This file shows that `ℝ` is a conditionally complete linearly ordered field.

Key result from mathlib:
[#3292](https://github.com/leanprover-community/mathlib/pull/3292)

-/

-- the reals are noncomputable in some precise sense.
noncomputable theory

-- enable notation `ℝ≥0` for the non-negative reals
open_locale nnreal

-- Lean's type class inference system (the "square bracket system") can supply a proof
-- that the reals are a conditionally complete linearly ordered field.
example : conditionally_complete_linear_ordered_field ℝ := infer_instance

-- The non-negative reals are by definition the subtype of reals which are ≥ 0.
example : ℝ≥0 = {r : ℝ // r ≥ 0} := rfl

-- Any conditionally complete linear ordered field is isomorphic (as an ordered ring) to `ℝ`.
-- Note that `≃+*o` is notation for "an isomorphism of ordered rings".
example {R : Type*} [conditionally_complete_linear_ordered_field R] : R ≃+*o ℝ := default

-- The isomorphism above is unique
example {R : Type*} [conditionally_complete_linear_ordered_field R] (e₁ e₂ : R ≃+*o ℝ) :
  e₁ = e₂ := subsingleton.elim _ _
