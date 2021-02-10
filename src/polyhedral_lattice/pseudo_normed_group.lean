import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.with_Tinv

import for_mathlib.topological_group
import for_mathlib.topology

import facts

noncomputable theory
open_locale nnreal

namespace polyhedral_lattice

open pseudo_normed_group normed_group

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
  classical,
  have aux := filtration_finite Λ 1,
  let s := aux.to_finset,
  let s₀ := s.erase 0,
  by_cases hs₀ : s₀.nonempty,
  { let ε : ℝ≥0 := finset.min' (s₀.image $ nnnorm) (hs₀.image _),
    obtain ⟨a, has₀, ha⟩ : ∃ a ∈ s₀, nnnorm a = ε,
    { rw ← finset.mem_image, apply finset.min'_mem },
    have H : 0 < ∥a∥ := by simpa only [norm_pos_iff] using finset.ne_of_mem_erase has₀,
    have h0ε : 0 < ε, { simpa only [← ha] },
    have hε1 : ε ≤ 1,
    { replace has₀ := finset.mem_of_mem_erase has₀,
      simp only [set.finite.mem_to_finset, mem_filtration_iff, nnreal.coe_one] at has₀,
      rwa [← ha] },
    suffices : ({0} : set Λ) = ball (0:Λ) ε,
    { rw this, apply is_open_ball },
    ext,
    simp only [metric.mem_ball, set.mem_singleton_iff, dist_zero_right],
    split,
    { rintro rfl, rw norm_zero, exact_mod_cast h0ε },
    intro h,
    have hx : x ∈ s,
    { simp only [set.finite.mem_to_finset, mem_filtration_iff, nnreal.coe_one],
      exact le_of_lt (lt_of_lt_of_le h hε1) },
    by_contra hx0,
    replace hx := finset.mem_erase_of_ne_of_mem hx0 hx,
    have := finset.min'_le (s₀.image $ nnnorm),
    refine not_lt.2 (this (nnnorm x) _) h,
    simp only [exists_prop, set.finite.mem_to_finset, finset.mem_image],
    use ⟨x, ⟨hx, rfl⟩⟩ },
  { suffices : ({0} : set Λ) = ball (0:Λ) 1,
    { rw this, apply is_open_ball },
    ext,
    simp only [metric.mem_ball, set.mem_singleton_iff, dist_zero_right],
    split,
    { rintro rfl, rw norm_zero, exact zero_lt_one },
    intro h,
    contrapose! hs₀,
    refine ⟨x, _⟩,
    simp only [set.finite.mem_to_finset, finset.mem_erase, mem_filtration_iff, nnreal.coe_one],
    exact ⟨hs₀, h.le⟩ }
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

variables {Λ r' M} (c : ℝ≥0)

def incl (c : ℝ≥0) : filtration (Λ →+ M) c → Π l : Λ, filtration M (c * nnnorm l) :=
λ f l, ⟨f l, f.2 $ normed_group.mem_filtration_nnnorm _⟩

@[simp] lemma coe_incl_apply (f : filtration (Λ →+ M) c) (l : Λ) :
  (incl c f l : M) = f l :=
rfl

variables (Λ r' M)

lemma incl_injective : function.injective (@incl Λ r' M _ _ _ c) :=
begin
  intros f g h,
  ext l,
  show (incl c f l : M) = incl c g l,
  rw h
end

instance : topological_space (filtration (Λ →+ M) c) :=
topological_space.induced (incl c) infer_instance

lemma incl_embedding : embedding (@incl Λ r' M _ _ _ c) :=
{ induced := rfl,
  inj := incl_injective Λ r' M c }

lemma incl_inducing : inducing (@incl Λ r' M _ _ _ c) := ⟨rfl⟩

lemma incl_continuous : continuous (@incl Λ r' M _ _ _ c) :=
(incl_inducing _ _ _ _).continuous

instance : t2_space (filtration (Λ →+ M) c) :=
(incl_embedding Λ r' M c).t2_space

instance : totally_disconnected_space (filtration (Λ →+ M) c) :=
(incl_embedding Λ r' M c).totally_disconnected_space

lemma incl_range_eq :
  (set.range (@incl Λ r' M _ _ _ c)) =
    ⋂ l₁ l₂, {f | (cast_le (f (l₁ + l₂)) : filtration M (c * (nnnorm l₁ + nnnorm l₂))) =
    cast_le (add' (f l₁, f l₂))} :=
begin
  ext f,
  simp only [set.mem_range, set.mem_Inter, coe_fn_coe_base, coe_incl_apply,
    set.mem_set_of_eq, subtype.coe_mk, subtype.ext_iff],
  split,
  { rintro ⟨⟨f, hf⟩, rfl⟩ l₁ l₂,
    exact f.map_add _ _ },
  { intro h,
    refine ⟨⟨add_monoid_hom.mk' (λ l, f l) h, _⟩, _⟩,
    { intros c' l hl,
      rw mem_filtration_iff at hl,
      exact filtration_mono (mul_le_mul' le_rfl hl) (f l).2 },
    { ext, refl } }
end

open profinitely_filtered_pseudo_normed_group

lemma incl_range_is_closed : (is_closed (set.range (@incl Λ r' M _ _ _ c))) :=
begin
  rw incl_range_eq,
  apply is_closed_Inter,
  intro l₁,
  apply is_closed_Inter,
  intro l₂,
  apply is_closed_eq,
  { exact (continuous_cast_le _ _).comp (continuous_apply (l₁ + l₂)) },
  { exact (continuous_cast_le _ _).comp ((continuous_add' _ _).comp
          ((continuous_apply l₁).prod_mk (continuous_apply l₂))) },
end

instance : compact_space (filtration (Λ →+ M) c) :=
{ compact_univ :=
  begin
    apply (incl_inducing Λ r' M c).is_compact _,
    apply is_closed.compact,
    rw set.image_univ,
    exact incl_range_is_closed _ _ _ _
  end }

lemma continuous_iff {X : Type*} [topological_space X]
  (ϕ : X → (filtration (Λ →+ M) c)) :
  continuous ϕ ↔ ∀ l : Λ, continuous (λ x, incl c (ϕ x) l) :=
begin
  rw (incl_inducing Λ r' M c).continuous_iff,
  split,
  { intros h l, exact (continuous_apply l).comp h },
  { exact continuous_pi }
end

instance profinitely_filtered_pseudo_normed_group :
  profinitely_filtered_pseudo_normed_group (Λ →+ M) :=
{ continuous_add' :=
  begin
    intros c₁ c₂,
    rw continuous_iff,
    intro l,
    have step1 :=
      ((continuous_apply l).comp (incl_continuous Λ r' M c₁)).prod_map
      ((continuous_apply l).comp (incl_continuous Λ r' M c₂)),
    have step2 := (continuous_add' (c₁ * nnnorm l) (c₂ * nnnorm l)),
    have := step2.comp step1,
    refine (@continuous_cast_le _ _ _ _ (id _)).comp this,
    rw add_mul, exact le_rfl
  end,
  continuous_neg' :=
  begin
    intro c,
    rw continuous_iff,
    intro l,
    exact (continuous_neg' _).comp ((continuous_apply l).comp (incl_continuous Λ r' M c)),
  end,
  continuous_cast_le :=
  begin
    introsI c₁ c₂ h,
    rw continuous_iff,
    intro l,
    exact (continuous_cast_le _ _).comp ((continuous_apply l).comp (incl_continuous Λ r' M c₁))
  end,
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

open profinitely_filtered_pseudo_normed_group

def Tinv : profinitely_filtered_pseudo_normed_group_hom (Λ →+ M) (Λ →+ M) :=
profinitely_filtered_pseudo_normed_group_hom.mk' Tinv'
begin
  refine ⟨r'⁻¹, λ c, ⟨Tinv'_mem_filtration c, _⟩⟩,
  rw add_monoid_hom.continuous_iff,
  intro l,
  refine (@continuous_cast_le _ _ _ _ (id _)).comp
    ((@Tinv₀_continuous r' M _ (c * nnnorm l)).comp
    ((continuous_apply l).comp (add_monoid_hom.incl_continuous Λ r' M c))),
  rw mul_assoc, exact le_rfl
end

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Λ →+ M) :=
{ Tinv := Tinv Λ r' M,
  Tinv_mem_filtration := Tinv'_mem_filtration,
  .. add_monoid_hom.profinitely_filtered_pseudo_normed_group Λ r' M }

end polyhedral_lattice
