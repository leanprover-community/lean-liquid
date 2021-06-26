import pseudo_normed_group.system_of_complexes
import Mbar.pseudo_normed_group
import breen_deligne.homotopy

.

open_locale nnreal

open category_theory ProFiltPseuNormGrpWithTinv opposite

variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]
variables (BD : breen_deligne.package) (κ : ℕ → ℝ≥0)
variables [BD.data.very_suitable r r' κ] [∀ (i : ℕ), fact (0 < κ i)]

include r r' BD κ

def first_target_stmt : Prop :=
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : SemiNormedGroup.{0}) [normed_with_aut r V],
    ​((BD.data.system κ r V r').obj (op $ of r' (Mbar r' S))).is_weak_bounded_exact k K m c₀
