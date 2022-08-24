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
example (r : ℝ) (v : V) : ∥r • v∥ = |r|^(p : ℝ) * ∥v∥ :=
(p_banach.exists_p_norm V.p_banach').some.norm_smul r v

/- The chosen norm on $V$ satisfies the triangle inequality -/
example (v w : V) : ∥v + w∥ ≤ ∥v∥ + ∥w∥ :=
(p_banach.exists_p_norm V.p_banach').some.triangle v w

/- The uniform space structure on `V` is induced by the chosen norm. -/
example : uniformity V = ⨅ (ε : ℝ) (H : ε > 0),
  filter.principal { p : V × V | ∥p.1 - p.2∥ < ε } :=
(p_banach.exists_p_norm V.p_banach').some.uniformity

end pBanach

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

/-- An example of a p-Banach space. -/
example [fact (0 < p)] [fact (p ≤ 1)] : pBanach p :=
pBanach.lp p

/-- Elements of `pBanach.lp p` can be considered as functions `ℕ → ℝ`. -/
example [fact (0 < p)] [fact (p ≤ 1)] (f : pBanach.lp p) : ℕ → ℝ :=
λ i, f i

/-- Given an element of `pBanach.lp p`, the sum `∑' n, | f n |^p` exists. -/
example [fact (0 < p)] [fact (p ≤ 1)] (f : pBanach.lp p) :
  summable (λ n, | f n |^(p : ℝ)) :=
pBanach.lp_type.summable f

/-- The ℝ-module structure behaves as expected. -/
example [fact (0 < p)] [fact (p ≤ 1)] (f g : pBanach.lp p) (n : ℕ) :
  (f + g) n = f n + g n := rfl

example [fact (0 < p)] [fact (p ≤ 1)] (a : ℝ) (f : pBanach.lp p) (n : ℕ) :
  (a • f) n = a * f n := rfl

/-- Conversely, we can construct elements of `pBanach.lp p` using sequences where the
  sum above exists. -/
example [fact (0 < p)] [fact (p ≤ 1)] (f : ℕ → ℝ) (hf : summable (λ n, | f n |^(p : ℝ))) :
  pBanach.lp p :=
{ val := f,
  property := begin
    change ite _ _ _,
    rw if_neg, rw if_neg, assumption,
    exact ennreal.coe_ne_top,
    exact (ne_of_gt $ by exact_mod_cast (fact.out (0 < p))),
  end }

example [fact (0 < p)] [fact (p ≤ 1)] : nontrivial (pBanach.lp p) := infer_instance
