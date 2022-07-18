import challenge_notations
import challenge_prerequisites

/-!

This file explains how the condensed abelian group associated to a p-Banach space `V` behaves.

-/

noncomputable theory

open_locale liquid_tensor_experiment nnreal zero_object
open liquid_tensor_experiment category_theory category_theory.limits opposite

variables (p : ℝ≥0) (V : pBanach.{0} p) (S : Profinite.{0})

section pBanach

example : topological_add_group V := infer_instance

example : module ℝ V := infer_instance

example : has_continuous_smul ℝ V := infer_instance

example : complete_space V := infer_instance

example : separated_space V := infer_instance

/-- A p-Banach space has a norm. -/
def pBanach.has_norm : has_norm V :=
(p_banach.exists_p_norm V.p_banach').some.to_has_norm

local attribute [instance] pBanach.has_norm

example (r : ℝ) (v : V) : ∥ r • v ∥ = |r|^(p : ℝ) * ∥ v ∥ :=
(p_banach.exists_p_norm V.p_banach').some.norm_smul r v

example (v w : V) : ∥ v + w ∥ ≤ ∥ v ∥ + ∥ w ∥ :=
(p_banach.exists_p_norm V.p_banach').some.triangle v w

/- The uniform space structure on `V` is induced by the norm. -/
example : uniformity V = ⨅ (ε : ℝ) (H : ε > 0),
  filter.principal { p : V × V | ∥ p.fst - p.snd ∥ < ε } :=
(p_banach.exists_p_norm V.p_banach').some.uniformity

end pBanach

example :
  ((Condensed_Ab_to_presheaf.{0}.obj V).obj (op S) : Type 1) = ulift C(S,V) :=
rfl

example (f : C(S,V)) : S → V := f
example (f : C(S,V)) : continuous f := f.continuous
example (f : S → V) (hf : continuous f) : C(S,V) := ⟨f,hf⟩

example (f g : (Condensed_Ab_to_presheaf.{0}.obj V).obj (op S)) (s : S) :
  (f + g) s = f s + g s :=
rfl
