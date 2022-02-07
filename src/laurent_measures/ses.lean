-- import laurent_measures.functor
import laurent_measures.thm69
-- import data.real.basic

/-
This files introduces the maps `Θ`, `Φ` and `Ψ` are the "measurifications" of `θ`, `ϕ` and `ψ` from
`laurent_measures.thm69`, they are morphisms in the right category.

We then prove in **???** that `θ_ϕ_exact` of `laurent_measures.thm69` becomes a short exact sequence
in the category **???**.
-/


noncomputable theory

namespace laurent_measures_ses

open nnreal laurent_measures
open_locale big_operators nnreal

section homs

parameter {p : ℝ≥0}

def r : ℝ≥0 := (1 / 2) ^ (p:ℝ)

variables [fact(0 < p)] [fact (p < 1)]
variables [fact (0 < r)]
variable {S : Fintype}

local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

example : profinitely_filtered_pseudo_normed_group_with_Tinv r (ℒ S) :=
begin
  apply_instance,
end

-- begin

-- end

end homs

end laurent_measures_ses
