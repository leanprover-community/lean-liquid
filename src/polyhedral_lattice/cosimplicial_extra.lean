import polyhedral_lattice.cosimplicial
import polyhedral_lattice.Hom

import combinatorial_lemma -- for `add_monoid_hom_mem_filtration_iff` (move it)

open_locale nnreal

namespace PolyhedralLattice

open pseudo_normed_group polyhedral_lattice.conerve (L obj lift' lift'_w)

variables (r' : ℝ≥0) (Λ : PolyhedralLattice)
variables (M : ProFiltPseuNormGrpWithTinv r') (N : ℕ) [fact (0 < N)]
variables (m : ℕ) (g₀ : Λ →+ M)
variables (g : fin (m + 1) → (Λ.rescaled_power N →+ M))
variables (hg : ∀ i l, (g i) (Λ.diagonal_embedding N l) = g₀ l)

lemma cosimplicial_lift_mk (l) :
  Λ.cosimplicial_lift N m g₀ g hg (quotient_add_group.mk l) = finsupp.lift_add_hom g l :=
begin
  dsimp only [cosimplicial_lift, lift'],
  have := quotient_add_group.lift_mk'
    (L (Λ.diagonal_embedding N) (m + 1))
    (lift'_w (Λ.diagonal_embedding N) m g₀ g hg _) l,
  exact this,
end

lemma cosimplicial_lift_mem_filtration (c : ℝ≥0)
  (H : ∀ i, g i ∈ filtration ((Λ.rescaled_power N) →+ M) c) :
  cosimplicial_lift Λ N m g₀ g hg ∈ filtration (obj (Λ.diagonal_embedding N) (m + 1) →+ M) c :=
begin
  intros c' l' hl,
  obtain ⟨J, _instJ, x, hx⟩ := polyhedral_lattice.polyhedral' Λ, resetI,
  obtain ⟨l, rfl⟩ : ∃ l, quotient_add_group.mk l = l',
  { exact quotient.surjective_quotient_mk' l' },
  rw cosimplicial_lift_mk,
  let x' : (fin N) × J → Λ.rescaled_power N :=
    generates_norm.rescale_generators N _ (generates_norm.finsupp_generators (fin N) Λ x),
  have hx' : generates_norm x' := (hx.finsupp (fin N)).rescale N,
  have aux := λ i, hx'.generates_nnnorm (l i),
  choose C h1 h2 using aux,
  rw [finsupp.lift_add_hom_apply],
  -- rw [generates_norm.add_monoid_hom_mem_filtration_iff],
  sorry
end

end PolyhedralLattice
