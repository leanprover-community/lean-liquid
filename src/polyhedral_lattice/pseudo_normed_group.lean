import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.with_Tinv

import for_mathlib.topological_group

noncomputable theory
open_locale nnreal

namespace polyhedral_lattice

open pseudo_normed_group

variables (Λ : Type*) (r' : ℝ≥0) (M : Type*)
variables [normed_group Λ] [polyhedral_lattice Λ]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]

lemma filtration_finite (c : ℝ≥0) : (filtration Λ c).finite :=
begin
  obtain ⟨s, hs₀, hs⟩ := polyhedral_lattice.polyhedral' Λ,
  sorry
end

open metric

instance : discrete_topology Λ :=
discrete_topology_of_open_singleton_zero _ $
begin
  have aux := filtration_finite Λ 1,
  let s := (filtration Λ 1) \ {0},
  have s_fin : s.finite,
  { sorry },
  let s₀ : finset Λ := s_fin.to_finset,
  by_cases hs₀ : s₀.nonempty,
  { let ε : ℝ≥0 := finset.min' (s₀.image $ nnnorm) (hs₀.image _),
    suffices : ({0} : set Λ) = ball (0:Λ) (ε/2),
    { rw this, apply is_open_ball },
    sorry },
  sorry
end

instance filtration_fintype (c : ℝ≥0) : fintype (filtration Λ c) :=
(filtration_finite Λ c).fintype

instance : profinitely_filtered_pseudo_normed_group Λ :=
{ compact := λ c, by apply_instance, -- compact of finite
  continuous_add' := λ _ _, continuous_of_discrete_topology,
  continuous_neg' := λ _, continuous_of_discrete_topology,
  continuous_cast_le := λ _ _ _, continuous_of_discrete_topology,
  .. (show pseudo_normed_group Λ, by apply_instance) }

include r'

namespace add_monoid_hom

variables {Λ r' M}

def incl (c : ℝ≥0) : filtration (Λ →+ M) c → Π l : Λ, filtration M (c * nnnorm l) :=
λ f l, ⟨f l, f.2 $ normed_group.mem_filtration_nnnorm _⟩

@[simp] lemma coe_incl_apply (c : ℝ≥0) (f : filtration (Λ →+ M) c) (l : Λ) :
  (incl c f l : M) = f l :=
rfl

variables (Λ r' M) (c : ℝ≥0)

instance : topological_space (filtration (Λ →+ M) c) :=
topological_space.induced (incl c) infer_instance

-- this should be `by apply_instance`
instance : t2_space (filtration (Λ →+ M) c) :=
sorry

-- this should be `by apply_instance`
instance : totally_disconnected_space (filtration (Λ →+ M) c) :=
sorry

-- need to prove that the range of `incl c` is closed
instance : compact_space (filtration (Λ →+ M) c) :=
sorry

instance profinitely_filtered_pseudo_normed_group :
  profinitely_filtered_pseudo_normed_group (Λ →+ M) :=
{ continuous_add' := sorry,
  continuous_neg' := sorry,
  continuous_cast_le := sorry,
  .. add_monoid_hom.pseudo_normed_group }

end add_monoid_hom

variables {Λ r' M}

open profinitely_filtered_pseudo_normed_group_with_Tinv

def Tinv' : (Λ →+ M) →+ (Λ →+ M) :=
add_monoid_hom.comp_hom
  (@Tinv r' M _).to_add_monoid_hom

@[simp] lemma Tinv'_apply (f : Λ →+ M) (l : Λ) :
  Tinv' f l = Tinv (f l) := rfl

lemma Tinv'_mem_filtration (c : ℝ≥0) (f : Λ →+ M) (hf : f ∈ filtration (Λ →+ M) c) :
  Tinv' f ∈ filtration (Λ →+ M) (r'⁻¹ * c) :=
begin
  intros x l hl,
  rw [Tinv'_apply, mul_assoc],
  apply Tinv_mem_filtration,
  exact hf hl
end

variables (Λ r' M)

def Tinv : profinitely_filtered_pseudo_normed_group_hom (Λ →+ M) (Λ →+ M) :=
profinitely_filtered_pseudo_normed_group_hom.mk' Tinv'
begin
  refine ⟨r'⁻¹, λ c, ⟨Tinv'_mem_filtration c, _⟩⟩,
  sorry
end

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Λ →+ M) :=
{ Tinv := Tinv Λ r' M,
  Tinv_mem_filtration := Tinv'_mem_filtration,
  .. add_monoid_hom.profinitely_filtered_pseudo_normed_group Λ r' M }

end polyhedral_lattice
