import analysis.normed_space.basic
import ring_theory.finiteness

import hacks_and_tricks.by_exactI_hack

open_locale big_operators

section move_this

-- rewrite to include multiplicative version
def torsion_free (A : Type*) [add_comm_group A] : Prop :=
∀ (a : A) (n : ℕ), n • a = 0 → n = 0

end move_this

class polyhedral_lattice (A : Type*) [normed_group A] :=
(tf : torsion_free A)
(polyhedral' [] : ∃ s : finset A, submodule.span ℤ (s : set A) = ⊤ ∧
              ∀ n : {a // a ∈ s} → ℤ, ∥∑ a, n a • a.1∥ = ∑ a, n a • ∥a.1∥)

namespace polyhedral_lattice

variables (A : Type*) [normed_group A] [polyhedral_lattice A]

instance : module.finite ℤ A :=
begin
  obtain ⟨s, h1, h2⟩ := polyhedral_lattice.polyhedral' A,
  exact ⟨s, h1⟩
end

-- lemma polyhedral : ∃ (ι : Type*) [fintype ι] (a : ι → A),
--   submodule.span ℤ (set.range a) = ⊤ ∧
--   ​∀ n : ι → ℤ, ∥∑ i, n i • a i∥ = ∑ i, n i • ∥a i∥ :=
-- begin
--   obtain ⟨s, h1, h2⟩ := polyhedral_lattice.polyhedral' A,
--   refine ⟨{a // a ∈ s}, _⟩,
-- end

end polyhedral_lattice
