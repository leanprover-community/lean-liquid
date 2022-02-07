import laurent_measures.functor
import laurent_measures.thm69


/-
This files introduces the maps `Θ`, `Φ` and `Ψ` are the "measurifications" of `θ`, `ϕ` and `ψ` from
`laurent_measures.thm69`, they are morphisms in the right category.

We then prove in **???** that `θ_ϕ_exact` of `laurent_measures.thm69` becomes a short exact sequence
in the category **???**.-/


noncomputable theory

namespace laurent_measures_ses

section homs

parameter {p : ℝ≥0}

def r : ℝ≥0 := (1 / 2) ^ (p:ℝ)

variables [fact(0 < p)] [fact (p < 1)]
variable {S : Fintype}


example : profinitely_filtered_pseudo_normed_group_with_Tinv r (ℒ S) := by library_search

end homs
