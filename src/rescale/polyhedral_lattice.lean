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

namespace generates_norm

open rescale

variables (N : ℝ≥0) (Λ : Type*)

def rescale_generators {J : Type*} (x : J → Λ) : J → (rescale N Λ) := x
variables [add_comm_monoid Λ] [has_norm Λ] {J : Type*} [fintype J] (x : J → Λ) (hx : generates_norm x)

variables {Λ x}

include hx

lemma rescale : generates_norm (rescale_generators N Λ x) :=
begin
  intro l,
  obtain ⟨c, H1, H2⟩ := hx l,
  refine ⟨c, H1, _⟩,
  simp only [norm_def, ← mul_div_assoc, ← finset.sum_div],
  congr' 1,
end

end generates_norm

namespace rescale

variables {N : ℝ≥0} {V : Type*}

instance (Λ : Type*) [hN : fact (0 < N)] [polyhedral_lattice Λ] :
  polyhedral_lattice (rescale N Λ) :=
{ finite := by { delta rescale, apply_instance },
  free   := by { delta rescale, apply_instance },
  polyhedral' :=
  begin
    obtain ⟨ι, _inst_ι, l, hl⟩ := polyhedral_lattice.polyhedral' Λ, resetI,
    refine ⟨ι, _inst_ι, l, hl.rescale N⟩,
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
