import ring_theory.finiteness
import linear_algebra.free_module
import linear_algebra.dual

open_locale big_operators

variables (R M : Type*) [ring R] [add_comm_group M] [module R M]

section
variables [module.finite ℤ M] [module.free ℤ M]

-- generalize?
instance : module.finite ℤ (M →+ ℤ) :=
begin
  classical,
  let b := module.free.choose_basis ℤ M,
  exact module.finite.of_basis (b.dual_basis.map add_monoid_hom_lequiv_int.symm),
end

-- generalize?
instance : module.free ℤ (M →+ ℤ) :=
begin
  classical,
  let b := module.free.choose_basis ℤ M,
  exact module.free.of_basis (b.dual_basis.map add_monoid_hom_lequiv_int.symm),
end

end
