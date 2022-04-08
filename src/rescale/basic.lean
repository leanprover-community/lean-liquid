import polyhedral_lattice.basic
/-!

# rescaling the norm on a type

This file is little more than the definition of the type alias.

-/
noncomputable theory
open_locale big_operators classical nnreal

/-- `rescale r M` is the pseudo-normed group `M` but with a new filtration,
where `(rescale r M)_c := M_{c*r⁻¹}`.
-/
@[nolint unused_arguments]
def rescale (N : ℝ≥0) (V : Type*) := V

namespace rescale

variables {N : ℝ≥0} {V : Type*}

instance [i : add_comm_monoid V] : add_comm_monoid (rescale N V) := i
instance [i : add_comm_group V] : add_comm_group (rescale N V) := i

def of : V ≃ rescale N V := equiv.refl _

end rescale
