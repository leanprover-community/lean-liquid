import breen_deligne
import system_of_complexes
import locally_constant.Vhat
import Mbar.complex

open_locale nnreal

variables (r r' : ℝ) (h0r : 0 < r) (hrr' : r < r') (hr'1 : r < 1)
variables (c : ℕ+ → ℝ) -- implicit constants, chosen once and for all
                       -- see the sentence after that statement of Thm 9.5
variables (S : Type) [hS : fintype S]
variables (V : Type)

include h0r hrr' hr'1 c

/-- Thm 9.5 in `Analytic.pdf` -/
theorem main :
  ∀ m : ℕ,
  ∃ (k : ℝ≥0) (hk : fact (1 ≤ k)),
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : Type),
  begin
    resetI,
    refine system_of_complexes.is_bdd_exact_for_bdd_degree_above_idx _ k m c₀,
    refine @Mbar_invariants r r' h0r hrr' hr'1 c S (id _) V,
    resetI,
    assumption',
  end :=
sorry
