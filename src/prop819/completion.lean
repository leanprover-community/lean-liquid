import for_mathlib.SemiNormedGroup
import algebra.homology.additive
import locally_constant.Vhat

noncomputable theory

variables (C : cochain_complex SemiNormedGroup ℕ)

abbreviation cmpl := (SemiNormedGroup.Completion.map_homological_complex _).obj C

open_locale nnreal

lemma cmpl_exact_of_exact (ε : ℝ≥0) (hε : 0 < ε)
  (cond : ∀ (n : ℕ) (f : C.X n) (hf : C.d_from n f = 0),
    ∃ g : C.X_prev n, C.d_to n g = f ∧ ∥ g ∥ ≤ ∥ f ∥) (n : ℕ) (f : ((cmpl C).X n))
    (hf : (cmpl C).d_from _ f = 0) : ∃ g : (cmpl C).X_prev n, (cmpl C).d_to _ g = f ∧
    ∥ g ∥ ≤ (1 + ε) * ∥ f ∥ := sorry
