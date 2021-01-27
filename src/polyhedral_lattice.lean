import analysis.normed_space.basic
import ring_theory.finiteness

import hacks_and_tricks.by_exactI_hack

noncomputable theory
open_locale big_operators

section move_this

-- rewrite to include multiplicative version
def torsion_free (A : Type*) [add_comm_group A] : Prop :=
∀ (a : A) (ha : a ≠ 0) (n : ℕ), n • a = 0 → n = 0

end move_this

class polyhedral_lattice (A : Type*) [normed_group A] :=
(tf : torsion_free A)
(polyhedral' [] : sorry)

namespace polyhedral_lattice

variables (A : Type*) [normed_group A] [polyhedral_lattice A]

instance : module.finite ℤ A :=
sorry

instance int : polyhedral_lattice ℤ :=
{ tf := λ m hm n h,
  begin
    rw [← nsmul_eq_smul, nsmul_eq_mul, mul_eq_zero] at h,
    simpa only [hm, int.coe_nat_eq_zero, or_false, int.nat_cast_eq_coe_nat] using h
  end,
  polyhedral' := sorry }

end polyhedral_lattice
