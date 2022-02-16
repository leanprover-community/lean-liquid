import analysis.normed_space.int

import polyhedral_lattice.basic

/-!

# The integers are a polyhedral lattice.

The integers, with its usual norm, are a polyhedral lattice.

-/
noncomputable theory

open_locale big_operators

lemma int.sum_units_to_nat_smul (n : ℤ) :
  ∑ (i : units ℤ), int.to_nat (i * n) • (i : ℤ) = n :=
begin
  rw [units_int.univ, finset.sum_insert], swap, dec_trivial,
  simp only [mul_one, int.nat_cast_eq_coe_nat, one_mul, nsmul_eq_mul,
    units.coe_one, units.coe_neg_one, finset.sum_singleton,
    ← sub_eq_add_neg, int.to_nat_sub_to_nat_neg, neg_mul, mul_neg],
end

instance int.polyhedral_lattice : polyhedral_lattice ℤ :=
{ polyhedral' :=
  begin
    refine ⟨units ℤ, infer_instance, coe, _⟩,
    intro n,
    refine ⟨λ e, int.to_nat (e * n), (int.sum_units_to_nat_smul _).symm, _⟩,
    simp only [int.norm_coe_units, mul_one, nat.cast_one, one_mul, units_int.univ],
    show ∥n∥ = ((1 * n).to_nat) + (↑(((-1) * n).to_nat) + 0),
    simp only [neg_mul, add_zero, one_mul],
    exact (int.to_nat_add_to_nat_neg_eq_norm _).symm,
  end }
