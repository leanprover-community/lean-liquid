import rescale.normed_group
import polyhedral_lattice.category

/-!

# Rescaling the norm on a polyhedral lattice.

Rescaling the norm on a polyhedral lattice by a positive real factor gives a
polyhedral lattice (at least for us -- Scholze seem to demand a rationality
condition which we are missing).

-/

noncomputable theory
open_locale big_operators classical nnreal

namespace rescale

variables {N : ℝ≥0} {V : Type*}

instance (Λ : Type*) [hN : fact (0 < N)] [polyhedral_lattice Λ] :
  polyhedral_lattice (rescale N Λ) :=
{ finite_free := by { delta rescale, exact polyhedral_lattice.finite_free _ },
  polyhedral :=
  begin
    obtain ⟨ι, _inst_ι, l, hl, hl'⟩ := polyhedral_lattice.polyhedral Λ,
    refine ⟨ι, _inst_ι, l, _, _⟩,
    { intro x,
      obtain ⟨d, hd, c, H1, H2⟩ := hl x,
      refine ⟨d, hd, c, H1, _⟩,
      simp only [norm_def, ← mul_div_assoc, ← finset.sum_div],
      congr' 1, }, -- defeq abuse
    { intro i,
      simp only [nnnorm_def, ← pos_iff_ne_zero] at hl' ⊢,
      apply nnreal.div_pos (hl' i) hN.1, }
  end }

end rescale

namespace PolyhedralLattice

@[simps] protected def rescale (N : ℝ≥0) [hN : fact (0 < N)] :
  PolyhedralLattice ⥤ PolyhedralLattice :=
{ obj := λ Λ, of (rescale N Λ),
  map := λ Λ₁ Λ₂ f,
  { to_fun := λ l, @rescale.of N Λ₂ (f ((@rescale.of N Λ₁).symm l)),
    map_add' := f.map_add, -- defeq abuse
    strict' := λ l,
    begin
      simp only [← coe_nnnorm, nnreal.coe_le_coe],
      erw [rescale.nnnorm_def, rescale.nnnorm_def], simp only [div_eq_mul_inv],
      exact mul_le_mul' (f.strict l) le_rfl
    end } }

end PolyhedralLattice
