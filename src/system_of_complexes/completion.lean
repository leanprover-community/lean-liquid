import system_of_complexes.basic

open_locale nnreal

namespace system_of_complexes

universe variables u
variables (C C₁ C₂ : system_of_complexes.{u})
variables {k k' K K' : ℝ≥0} {m m' : ℤ} {c₀ c₀' : ℝ≥0} [fact (1 ≤ k)] [fact (1 ≤ k')]

def completion (C : system_of_complexes) : system_of_complexes := sorry

namespace is_weak_bdd_exact_for_bdd_degree_above_idx

lemma controlled_y (hC : C.is_weak_bdd_exact_for_bdd_degree_above_idx k K m c₀) :
∀ c ≥ c₀, ∀ i < m,
∀ x : C (k^2 * c) (i+1),
∀ (ε > 0) (δ > 0), ∃ y : C c i, ∥res x - d y∥ ≤ K * ∥d x∥ + ε ∧ ∥y∥ ≤ K*(K + 1)*∥x∥ + δ :=
sorry

lemma completion (hC : C.is_weak_bdd_exact_for_bdd_degree_above_idx k K m c₀) :
 C.completion.is_weak_bdd_exact_for_bdd_degree_above_idx (k^2) K m c₀ :=
sorry

lemma strong_of_complete (hC : C.is_weak_bdd_exact_for_bdd_degree_above_idx k K m c₀)
  (hC' : admissible C) :
  ∀ δ > 0, C.is_bdd_exact_for_bdd_degree_above_idx (k^2) (K + δ) m c₀ :=
sorry

end is_weak_bdd_exact_for_bdd_degree_above_idx

end system_of_complexes
