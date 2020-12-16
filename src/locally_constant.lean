import topology.subset_properties

variables {X Y : Type*} [topological_space X]

open_locale topological_space

def is_locally_constant (f : X → Y) : Prop := ∀ s, is_open (f ⁻¹' s)

namespace is_locally_constant

lemma exists_open {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
⟨f ⁻¹' {(f x)}, hf _, set.mem_singleton _, λ x' hx', set.mem_singleton_iff.mp hx'⟩

lemma exists_nhds {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∃ U ∈ 𝓝 x, ∀ x' ∈ U, f x' = f x :=
let ⟨U, hU, hx, H⟩ := hf.exists_open x in ⟨U, mem_nhds_sets hU hx, H⟩

lemma iff_exists_open (f : X → Y) :
  is_locally_constant f ↔ ∀ x, ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
begin
  refine ⟨exists_open, _⟩,
  assume h s,
  rw is_open_iff_forall_mem_open,
  assume x hx,
  obtain ⟨U, hU, hxU, H⟩ := h x,
  refine ⟨U, _, hU, hxU⟩,
  assume x' hx',
  simp only [*, set.mem_preimage] at *,
end

lemma iff_exists_nhds (f : X → Y) :
  is_locally_constant f ↔ ∀ x, ∃ U ∈ 𝓝 x, ∀ x' ∈ U, f x' = f x :=
begin
  refine ⟨exists_nhds, _⟩,
  assume h,
  rw iff_exists_open,
  assume x,
  obtain ⟨U, hU, H⟩ := h x,
  obtain ⟨V, hVU, hV, hxV⟩ : ∃ (V : set X) (H : V ⊆ U), is_open V ∧ x ∈ V,
  by rwa mem_nhds_sets_iff at hU,
  refine ⟨V, hV, hxV, _⟩,
  assume x' hx',
  solve_by_elim only [H, hxV, hx', hVU]
end

lemma of_constant (f : X → Y) (h : ∃ y, ∀ x, f x = y) :
  is_locally_constant f :=
begin
  obtain ⟨y, hy⟩ := h,
  rw iff_exists_nhds,
  intro x,
  refine ⟨set.univ, filter.univ_mem_sets, _⟩,
  rintro x -,
  rw [hy, hy]
end

lemma const (y : Y) : is_locally_constant (function.const X y) :=
of_constant _ ⟨y, λ _, rfl⟩

lemma continuous {_ : topological_space Y} {f : X → Y} (hf : is_locally_constant f) :
  continuous f :=
⟨λ U hU, hf _⟩

lemma iff_continuous {_ : topological_space Y} [discrete_topology Y] (f : X → Y) :
  is_locally_constant f ↔ _root_.continuous f :=
⟨continuous, λ h s, h.is_open_preimage s (is_open_discrete _)⟩

lemma map_eq_of_is_preconnected {f : X → Y} (hf : is_locally_constant f)
  (s : set X) (hs : is_preconnected s) (x y : X) (hx : x ∈ s) (hy : y ∈ s) :
  f y = f x :=
begin
  letI : topological_space Y := ⊥,
  haveI : discrete_topology Y := ⟨rfl⟩,
  have := is_preconnected.image hs f hf.continuous.continuous_on,
  sorry
end

end is_locally_constant
