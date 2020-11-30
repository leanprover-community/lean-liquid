import data.real.basic

import polyhedral_lattice
import laurent_polynomial

constant bdd_normed_module (r : ℝ) (R : Type) (V : Type) : Type

constant system_of_complexes : Type

constant system_of_complexes.is_bdd_exact_in_degree
  (C : system_of_complexes) (k : ℤ) (d : ℤ) : Prop


variables (r r' : ℝ) (h0r : 0 < r) (hrr' : r < r') (hr'1 : r < 1)
variables (c : ℕ+ → ℝ) -- implicit constants, chosen once and for all
                       -- see the sentence after that statement of Thm 9.5
variables (Λ : Type) [hΛ : polyhedral_lattice Λ]
variables (S : Type) [hS : fintype S]
variables (V : Type) [hV : bdd_normed_module r (laurent_polynomial ℤ) V]

include h0r hrr' hr'1 c hΛ hS hV

constant crazy_system_of_complexes (c' : ℝ) : system_of_complexes

omit hΛ hS hV

/-- Thm 9.5 in `Analytic.pdf` -/
theorem main :
  ∀ m : ℕ,
  ∃ k : ℕ,
  ∀ (Λ : Type) [polyhedral_lattice Λ],
  ∃ c₀ : ℝ,
  ∀ (S : Type) [fintype S],
  ∀ (V : Type) [bdd_normed_module r (laurent_polynomial ℤ) V],
  ∀ c' ≥ c₀, -- this `c'` is called `c` in `Analytic.pdf`,
             -- but that conflicts with the constants `c 1, c 2, c 3` that are "implicit"
  ∀ d ≤ m,
  begin
    refine system_of_complexes.is_bdd_exact_in_degree _ k d,
    refine @crazy_system_of_complexes r r' h0r hrr' hr'1 c Λ (id _) S (id _) V (id _) c',
    resetI,
    assumption',
  end :=
sorry
