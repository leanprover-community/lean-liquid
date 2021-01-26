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
(polyhedral' [] : ∃ s : finset A, submodule.span ℤ (s : set A) = ⊤ ∧
              ∀ n : {a // a ∈ s} → ℤ, ∥∑ a, n a • a.1∥ = ∑ a, ∥ n a ∥ • ∥a.1∥)

namespace polyhedral_lattice

variables (A : Type*) [normed_group A] [polyhedral_lattice A]

instance : module.finite ℤ A :=
begin
  obtain ⟨s, h1, h2⟩ := polyhedral_lattice.polyhedral' A,
  exact ⟨s, h1⟩
end

instance int : polyhedral_lattice ℤ :=
{ tf := λ m hm n h,
  begin
    rw [← nsmul_eq_smul, nsmul_eq_mul, mul_eq_zero] at h,
    simpa only [hm, int.coe_nat_eq_zero, or_false, int.nat_cast_eq_coe_nat] using h
  end,
  polyhedral' :=
  begin
    use {1},
    split,
    { simp [finset.coe_singleton],
      rw eq_top_iff,
      rintro n -,
      rw submodule.mem_span_singleton,
      use n,
      rw [← gsmul_eq_smul, gsmul_one, int.cast_id] },
    { intros x,
      let b : {a : ℤ // a ∈ ({1} : finset ℤ)} := ⟨1, by simp⟩,
      have : (finset.univ : finset {a // a ∈ ({1} : finset ℤ)}) = {b}, by tauto,
      simp only [this, mul_one, algebra.id.smul_eq_mul, eq_self_iff_true, finset.mem_singleton,
        finset.sum_singleton, subtype.coe_mk, norm_one, subtype.val_eq_coe],
      congr,
      exact gsmul_int_one _ },
  end }

-- lemma polyhedral : ∃ (ι : Type*) [fintype ι] (a : ι → A),
--   submodule.span ℤ (set.range a) = ⊤ ∧
--   ​∀ n : ι → ℤ, ∥∑ i, n i • a i∥ = ∑ i, n i • ∥a i∥ :=
-- begin
--   obtain ⟨s, h1, h2⟩ := polyhedral_lattice.polyhedral' A,
--   refine ⟨{a // a ∈ s}, _⟩,
-- end

end polyhedral_lattice
