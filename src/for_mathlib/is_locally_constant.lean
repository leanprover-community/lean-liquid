import topology.separation
import topology.locally_constant.basic
import topology.discrete_quotient
import data.setoid.partition

import for_mathlib.data_setoid_partition

noncomputable theory

variables {X : Type*} [topological_space X]

open set

section
variables {Y : Type*}

lemma is_locally_constant_iff_clopen_fibers {f : X → Y} :
  is_locally_constant f ↔ ∀ y, is_clopen (f ⁻¹' {y}) :=
⟨λ h y, h.is_clopen_fiber y, λ h s, (by { rw [← bUnion_of_singleton s, preimage_bUnion],
                                          exact is_open_bUnion (λ x _, (h x).1) })⟩
end

section
variables {Y : Type*}

def indexed_partition.discrete_quotient {ι : Type*} {s : ι → set X} (h_part : indexed_partition s)
  (h_cl : ∀ i, is_clopen $ s i) : discrete_quotient X :=
{ rel := h_part.setoid.rel,
  equiv := h_part.setoid.iseqv,
  clopen := begin
    intro x,
    rw h_part.class_of,
    apply h_cl
  end }

variables {ι : Type*} {s : ι → set X} (h_cl : ∀ i, is_clopen $ s i)
(h_part : indexed_partition s)

def indexed_partition.discrete_quotient_equiv : ι ≃ h_part.discrete_quotient h_cl :=
h_part.equiv_quotient


lemma indexed_partition.discrete_quotient_fiber (x : h_part.discrete_quotient h_cl) :
  (h_part.discrete_quotient h_cl).proj ⁻¹' {x} = s ((h_part.discrete_quotient_equiv h_cl).symm x) :=
h_part.proj_fiber _

end
