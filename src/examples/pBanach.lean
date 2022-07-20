import analysis.normed_space.lp_space
import challenge_notations
import challenge_prerequisites

/-!

This file explains how the condensed abelian group associated to a p-Banach space `V` behaves.

-/

noncomputable theory

open_locale liquid_tensor_experiment nnreal zero_object
open liquid_tensor_experiment category_theory category_theory.limits opposite

/-! Let $p$ be a nonnegative real, $V$ a $p$-Banach space, and $S$ a profinite set. -/
section pBanach

variables (p : ℝ≥0) (V : pBanach.{0} p) (S : Profinite.{0})

/-! The $p$-Banach space $V$ is a complete and separated topological $ℝ$-vector space. -/

example : topological_add_group V := infer_instance
example : module ℝ V := infer_instance
example : has_continuous_smul ℝ V := infer_instance
example : complete_space V := infer_instance
example : separated_space V := infer_instance

/--
We may *choose* a norm on the p-Banach space satisfying some properties
which will be discussed below.

NOTE: This is really *choice* that must be made, and we make this choice only within
the present section.
-/
def pBanach.has_norm : has_norm V :=
(p_banach.exists_p_norm V.p_banach').some.to_has_norm

/- We tell the typeclass system to use the norm chosen above. -/
local attribute [instance] pBanach.has_norm

/- The chosen norm on $V$ is a $p$-norm: it scales via the rule $∥rv∥ = |r|^p * ∥v∥$ -/
example (r : ℝ) (v : V) : ∥r • v∥ = |r|^(p : ℝ) * ∥v∥ :=
(p_banach.exists_p_norm V.p_banach').some.norm_smul r v

/- The chosen norm on $V$ satisfies the triangle inequality -/
example (v w : V) : ∥v + w∥ ≤ ∥v∥ + ∥w∥ :=
(p_banach.exists_p_norm V.p_banach').some.triangle v w

/- The uniform space structure on `V` is induced by the chosen norm. -/
example : uniformity V = ⨅ (ε : ℝ) (H : ε > 0),
  filter.principal { p : V × V | ∥p.1 - p.2∥ < ε } :=
(p_banach.exists_p_norm V.p_banach').some.uniformity

/- When $V$ is viewed as condensed abelian group, the sections
over $S$ are the continuous maps $S → V$.
For technical reasons related to size issues in topos theory,
we need to lift the space of continuous maps to a higher universe using `ulift`. -/
example : (Γ_ V S : Type 1) = ulift C(S,V) := rfl

/- Continuous maps behave as expected: they are continuous functions. -/
example (f : C(S,V)) : S → V := f
example (f : C(S,V)) : continuous f := f.continuous
example (f : S → V) (hf : continuous f) : C(S,V) := ⟨f,hf⟩

/- The group operation on `Γ_ V S` is pointwise addition, as expected. -/
example (f g : Γ_ V S) (s : S) : (f + g) s = f s + g s := rfl

end pBanach

section lp

open lp ennreal nnreal
open_locale ennreal

/- Although we restrict to `p ≤ 1`, it would be better to work with `p : ℝ≥0∞` rather than `p : ℝ≥0` because there is no coercion from `{x : ℝ≥0∞ // x ≤ 1}` to `{x : ℝ≥0 // x ≤ 1}`, for which the `simp` lemma `one_le_coe_iff` is needed. -/

variables {p : ℝ≥0} [hp : fact (p ≤ 1)]


/- We introduce the ℓ^q-space ℓ^q(T) for testing purposes.-/
variables {q q' : ℝ≥0∞} [fact (1 ≤ q)] {T : ℕ → Type*}
  [Π i, normed_group (T i)]
  [Π i, normed_space ℝ (T i)]
  [Π i, complete_space (T i)]

example : uniform_space (lp T q) := infer_instance --needs 1≤ q, no completeness and no normed space structure

example : topological_add_group (lp T q) := infer_instance --needs 1≤ q, no completeness and no normed space structure

-- example : metric_space (lp T q) := infer_instance --needs 1≤ q, no completeness and no normed space structure

example : separated_space (lp T q) := infer_instance--needs 1≤ q, no completeness and no normed space structure

example : has_continuous_smul ℝ (lp T q) := infer_instance  --needs 1 ≤ q, no completeness and no normed space structure

example : complete_space (lp T q) := infer_instance --needs 1 ≤ q, and completeness of every (F n)
/-The true example-/

def E : ℕ → Type* := λ n, ℝ
/-First, three basic instances to access `lp E p`-/
instance normed_group_En : Π n : ℕ, normed_group (E n) := by {intro _, unfold E, apply_instance}
instance normed_space_En : Π n : ℕ, normed_space ℝ (E n) := sorry --by {intro _, unfold E, apply_instance}
instance complete_space_En : Π n : ℕ, complete_space (E n) := sorry --by {intro _, unfold E, apply_instance}


/-Then, one instance to make the following lemmas type-check; and five lemmas corresponding to the relevant fields of `p_banach`-/

instance : metric_space (lp E p) := sorry --When `1 ≤ p`, this is a consequence of the ℓ^p(E) being a `normed_group`, but this is false when `p ≤ 1`.

lemma top_add_group_p_le_one : topological_add_group (lp E p) := sorry--would follow from a `normed_group` (→ `metric_space`) instance on `lp E p`

lemma cont_smul_p_le_one : has_continuous_smul ℝ (lp E p) := sorry

lemma complete_p_le_one : complete_space (lp E p ) := sorry

lemma separated_p_le_one : separated_space (lp E p) := infer_instance --sorry--would follow from a `normed_group` (→ `metric_space`) instance on `lp E p`

lemma p_norm_lp : has_p_norm (lp E p) p :=
begin
  have := has_norm.norm,
  rotate,
  use lp E p,
  apply_instance,
  use this;
  sorry,
end

--the following theorem should really be a `def`
theorem lp_N_is_pBanach : p_banach (lp E p) p :=
{ exists_p_norm := ⟨p_norm_lp⟩,
  topological_add_group := top_add_group_p_le_one,
  continuous_smul := cont_smul_p_le_one,
  complete := complete_p_le_one,
  separated := separated_p_le_one}

end lp
