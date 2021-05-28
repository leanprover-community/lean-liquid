import polyhedral_lattice.cosimplicial
import polyhedral_lattice.Hom

open_locale nnreal

namespace PolyhedralLattice

open pseudo_normed_group polyhedral_lattice.conerve (obj lift')

variables (r' : ℝ≥0) (Λ : PolyhedralLattice)
variables (M : ProFiltPseuNormGrpWithTinv r') (N : ℕ) [fact (0 < N)]
variables (m : ℕ) (g₀ : Λ →+ M)
variables (g : fin (m + 1) → (Λ.rescaled_power N →+ M))
variables (hg : ∀ i l, (g i) (Λ.diagonal_embedding N l) = g₀ l)

lemma cosimplicial_lift_mem_filtration (c : ℝ≥0)
  (H : ∀ i, g i ∈ filtration ((Λ.rescaled_power N) →+ M) c) :
  cosimplicial_lift Λ N m g₀ g hg ∈ filtration (obj (Λ.diagonal_embedding N) (m + 1) →+ M) c :=
begin
  intros c' l hl,
  dsimp only [cosimplicial_lift, lift'],
  sorry
end

end PolyhedralLattice
