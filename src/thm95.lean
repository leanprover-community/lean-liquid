import polyhedral_lattice.Hom
import Mbar.pseudo_normed_group

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.

variables (BD : breen_deligne.package)
variables (c' : ℕ → ℝ≥0)  -- implicit constants, chosen once and for all
                          -- see the sentence after the statement of Thm 9.5

open polyhedral_lattice

/-- Theorem 9.5 in [Analytic] -/
theorem thm95 [BD.suitable c']
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)] :
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∀ (Λ : Type) [polyhedral_lattice Λ],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : NormedGroup) [normed_with_aut r V],
    ​(BD.system c' r V r' (Hom Λ (Mbar r' S))).is_bounded_exact k K m c₀ :=
sorry
