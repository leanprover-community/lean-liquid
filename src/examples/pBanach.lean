import challenge_notations
import challenge_prerequisites

/-!

This file explains how the condensed abelian group associated to a p-Banach space `V` behaves.

-/

noncomputable theory

open_locale liquid_tensor_experiment nnreal zero_object
open liquid_tensor_experiment category_theory category_theory.limits opposite

/-! Let $p$ be a nonnegative real, $V$ a $p$-Banach space, and $S$ a profinite set. -/
variables (p : ℝ≥0) (V : pBanach.{0} p) (S : Profinite.{0})

section pBanach

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
example (r : ℝ) (v : V) : ∥ r • v ∥ = |r|^(p : ℝ) * ∥ v ∥ :=
(p_banach.exists_p_norm V.p_banach').some.norm_smul r v

/- The chosen norm on $V$ satisfies the triangle inequality -/
example (v w : V) : ∥ v + w ∥ ≤ ∥ v ∥ + ∥ w ∥ :=
(p_banach.exists_p_norm V.p_banach').some.triangle v w

/- The uniform space structure on `V` is induced by the chosen norm. -/
example : uniformity V = ⨅ (ε : ℝ) (H : ε > 0),
  filter.principal { p : V × V | ∥ p.fst - p.snd ∥ < ε } :=
(p_banach.exists_p_norm V.p_banach').some.uniformity

end pBanach

/- When $V$ is viewed as condensed abelian group, the sections
over $S$ are the continuous maps $S → V$.
For technical reasons related to size issues in topos theory,
we need to lift the space of continuous maps to a higher universe using `ulift`. -/
example : (Γ_ (V : Condensed.{0} Ab.{1}) S : Type 1) = ulift C(S,V) := rfl

/- Continuous maps behave as expected: they are continuous functions. -/
example (f : C(S,V)) : S → V := f
example (f : C(S,V)) : continuous f := f.continuous
example (f : S → V) (hf : continuous f) : C(S,V) := ⟨f,hf⟩

/- The group operation on `Γ_ V S` is pointwise addition, as expected. -/
example (f g : Γ_ (V : Condensed.{0} Ab.{1}) S) (s : S) :
  (f + g) s = f s + g s :=
rfl
