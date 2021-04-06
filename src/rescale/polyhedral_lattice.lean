import rescale.normed_group

/-!

# Rescaling the norm on a polyhedral lattice.

Rescaling the norm on a polyhedral lattice by a positive real factor gives a
polyhedral lattice (at least for us -- Scholze seem to demand a rationality
condition which we are missing).

-/

noncomputable theory
open_locale big_operators classical nnreal

local attribute [-instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

namespace rescale

variables {N : ℝ≥0} {V : Type*}

instance (Λ : Type*) [hN : fact (0 < N)] [polyhedral_lattice Λ] :
  polyhedral_lattice (rescale N Λ) :=
{ nat_semimodule := by { delta rescale, apply_instance },
  int_semimodule := by { delta rescale, apply_instance },
  is_scalar_tower := by { delta rescale, apply_instance },
  finite_free := by { delta rescale, exact polyhedral_lattice.finite_free },
  polyhedral :=
  begin
    obtain ⟨ι, _inst_ι, l, hl⟩ := polyhedral_lattice.polyhedral Λ,
    refine ⟨ι, _inst_ι, l, _⟩,
    intro x,
    obtain ⟨d, hd, c, H1, H2⟩ := hl x,
    refine ⟨d, hd, c, H1, _⟩,
    simp only [norm_def, ← mul_div_assoc, ← finset.sum_div],
    congr' 1, -- defeq abuse
  end }

end rescale
