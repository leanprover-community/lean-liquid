import polyhedral_lattice.cosimplicial
import polyhedral_lattice.Hom

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
  intros c' l' hl',
  rw [semi_normed_group.mem_filtration_iff] at hl',
  obtain ⟨l, rfl, hl⟩ := polyhedral_lattice.norm_lift _ l',
  erw cosimplicial_lift_mk,
  rw [finsupp.lift_add_hom_apply, finsupp.sum_fintype],
  swap, { intro, rw add_monoid_hom.map_zero },
  simp only [← coe_nnnorm, nnreal.eq_iff] at hl,
  erw [finsupp.nnnorm_def, finsupp.sum_fintype] at hl,
  swap, { intro, rw nnnorm_zero },
  rw ← hl at hl',
  replace hl' := mul_le_mul' (le_refl c) hl',
  rw [finset.mul_sum] at hl',
  apply filtration_mono hl',
  apply sum_mem_filtration,
  rintro i -,
  apply H,
  exact semi_normed_group.mem_filtration_nnnorm (l i),
end

end PolyhedralLattice
