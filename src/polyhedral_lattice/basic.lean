import analysis.normed_space.basic
import ring_theory.finiteness

import hacks_and_tricks.by_exactI_hack

noncomputable theory
open_locale big_operators classical

section move_this

-- rewrite to include multiplicative version
def torsion_free (A : Type*) [add_comm_group A] : Prop :=
∀ (a : A) (ha : a ≠ 0) (n : ℕ), n • a = 0 → n = 0

end move_this

class polyhedral_lattice (Λ : Type*) [normed_group Λ] :=
[fg : module.finite ℤ Λ]
(tf : torsion_free Λ)
(polyhedral' [] : ∃ (s : finset (Λ →+ ℚ)) (hs : s.nonempty),
  ∀ x : Λ, ∥x∥ = finset.max' (s.image $ λ f, f x) (hs.image _))

namespace polyhedral_lattice

variables (Λ : Type*) [normed_group Λ] [polyhedral_lattice Λ]

instance : module.finite ℤ Λ := fg

instance int : polyhedral_lattice ℤ :=
{ fg := by convert module.finite.self _,
  tf := λ m hm n h,
  begin
    rw [← nsmul_eq_smul, nsmul_eq_mul, mul_eq_zero] at h,
    simpa only [hm, int.coe_nat_eq_zero, or_false, int.nat_cast_eq_coe_nat] using h
  end,
  polyhedral' :=
  begin
    refine ⟨{int.cast_add_hom ℚ, -int.cast_add_hom ℚ}, finset.insert_nonempty _ _, _⟩,
    intro x,
    simp only [finset.image_insert, rat.cast_neg, finset.image_singleton,
      add_monoid_hom.neg_apply, rat.cast_coe_int, int.coe_cast_add_hom],
    sorry
  end }

end polyhedral_lattice
