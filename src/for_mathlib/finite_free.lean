import ring_theory.finiteness
import linear_algebra.free_module
import linear_algebra.dual

open_locale big_operators

variables (R M : Type*) [ring R] [add_comm_group M] [module R M]

section
variables [module.finite ℤ M] [module.free ℤ M]

-- generalize?
instance : module.finite ℤ (M →+ ℤ) :=
module.finite.equiv (add_monoid_hom_lequiv_int _).symm

-- generalize?
instance : module.free ℤ (M →+ ℤ) :=
module.free.of_equiv (add_monoid_hom_lequiv_int _).symm

end
