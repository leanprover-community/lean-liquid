import breen_deligne
import system_of_complexes
import locally_constant.Vhat
import Mbar.complex2

open_locale nnreal

variables
variables (BD : breen_deligne.package)
variables (c' : ℕ → ℝ≥0)  -- implicit constants, chosen once and for all
                          -- see the sentence after that statement of Thm 9.5

-- sanity check
lemma exists_suitable : ∃ c, BD.suitable c := sorry

/-- Thm 9.5 in `Analytic.pdf` -/
theorem main [BD.suitable c']
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)] :
  ∀ m : ℕ,
  ∃ (k : ℝ≥0) (hk : fact (1 ≤ k)),
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : NormedGroup) [normed_with_aut r V],
  by exactI (Mbar_system V S r r' BD c').is_bdd_exact_for_bdd_degree_above_idx k m c₀ :=
sorry

/-
TODO: we currently do not require that the maps in the complex are norm-nonincreasing
-/
