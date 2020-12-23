import breen_deligne
import system_of_complexes
import locally_constant.Vhat

variables (r r' : ℝ) (h0r : 0 < r) (hrr' : r < r') (hr'1 : r < 1)
variables (c : ℕ+ → ℝ) -- implicit constants, chosen once and for all
                       -- see the sentence after that statement of Thm 9.5
variables (S : Type) [hS : fintype S]
variables (V : Type)

include h0r hrr' hr'1 c hS V

constant crazy_system_of_complexes (c' : ℝ) : system_of_complexes

omit hS V

/-- Thm 9.5 in `Analytic.pdf` -/
theorem main :
  ∀ m : ℕ,
  ∃ k : ℕ,
  ∃ c₀ : ℝ,
  ∀ (S : Type) [fintype S],
  ∀ (V : Type),
  ∀ c' ≥ c₀, -- this `c'` is called `c` in `Analytic.pdf`,
             -- but that conflicts with the constants `c 1, c 2, c 3` that are "implicit"
  begin
    refine system_of_complexes.is_bdd_exact_for_bdd_degree _ k m,
    refine @crazy_system_of_complexes r r' h0r hrr' hr'1 c S (id _) V c',
    resetI,
    assumption',
  end :=
sorry
