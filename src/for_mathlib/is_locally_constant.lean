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

lemma is_locally_constant.is_closed_fiber
   {f : X → Y} (h : is_locally_constant f) (y : Y) :
  is_closed (f ⁻¹' {y}) :=
begin
  erw [← is_open_compl_iff, ← preimage_compl,
       show {y}ᶜ = ⋃ z (h : z ≠ y), ({z} : set Y), by { ext, simp },
       preimage_bUnion],
  exact is_open_bUnion (λ z hz, h {z}),
end

lemma is_locally_constant.is_clopen_fiber {f : X → Y}
  (h : is_locally_constant f) (y : Y): is_clopen (f ⁻¹' {y}) :=
⟨h.is_open_fiber y, h.is_closed_fiber y⟩

lemma is_locally_constant_iff_clopen_fibers {f : X → Y} :
  is_locally_constant f ↔ ∀ y, is_clopen (f ⁻¹' {y}) :=
⟨λ h y, h.is_clopen_fiber y, λ h s, (by { rw [← bUnion_of_singleton s, preimage_bUnion],
                                          exact is_open_bUnion (λ x _, (h x).1) })⟩
end

section
variables {Y : Type*}

/-- The discrete quotient of `X` associated to a locally constant `f : X → Y` is associated
to the relation `x ∼ x'` if `f x' = f x`. The weird ordering guarantees that
`{x' | x ∼ x'} = f ⁻¹' {x}`.
-/
def is_locally_constant.discrete_quotient {f : X → Y} (hf : is_locally_constant f) :
  discrete_quotient X :=
{ rel := λ x x', f x' = f x,
  equiv := ⟨λ _, rfl, λ x x', eq.symm, λ x₁ x₂ x₃ h h', by rwa h'⟩,
  clopen := λ x, hf.is_clopen_fiber (f x) }

/-- The map induced by a locally constant map `f : X → Y` from the associated discrete quotient
to `Y`. -/
def is_locally_constant.discrete_quotient_map {f : X → Y} (hf : is_locally_constant f) :
  hf.discrete_quotient → Y :=
@quotient.lift _ _ hf.discrete_quotient.setoid f (λ x x', eq.symm)

@[simp]
lemma is_locally_constant.discrete_quotient_map_proj_apply {f : X → Y} (hf : is_locally_constant f) (x : X) :
hf.discrete_quotient_map (hf.discrete_quotient.proj x) = f x := rfl

@[simp]
lemma is_locally_constant.discrete_quotient_map_proj {f : X → Y} (hf : is_locally_constant f) :
hf.discrete_quotient_map ∘ hf.discrete_quotient.proj = f := funext (λ x, rfl)


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
