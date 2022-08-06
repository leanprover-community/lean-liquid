import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.with_Tinv

import topology.connected

import facts
/-!

# If M is a profinitely filtered pseudo-normed group with T⁻¹ then so is Hom(Λ, M)

Here Λ is a polyhedral lattice, and the T⁻¹ is in the sense
of `pseudo_normed_group.with_Tinv`.

-/

noncomputable theory
open_locale nnreal big_operators

open pseudo_normed_group seminormed_add_comm_group

lemma int.one_mem_filtration : (1 : ℤ) ∈ filtration ℤ 1 :=
by simp only [nnnorm_one, mem_filtration_iff]

section

variables {Λ : Type*} [polyhedral_lattice Λ]
variables {M : Type*} [pseudo_normed_group M]

lemma generates_norm.add_monoid_hom_mem_filtration_iff {ι : Type} [fintype ι]
  {l : ι → Λ} (hl : generates_norm l) (x : Λ →+ M) (c : ℝ≥0) :
  x ∈ filtration (Λ →+ M) c ↔ ∀ i, x (l i) ∈ filtration M (c * ∥l i∥₊) :=
begin
  refine ⟨λ H i, H (le_refl ∥l i∥₊), _⟩,
  intros H c' l' hl',
  obtain ⟨cᵢ, h1, h2⟩ := hl.generates_nnnorm l',
  rw [h1, x.map_sum],
  refine filtration_mono _ (sum_mem_filtration _ (λ i, c * cᵢ i * ∥l i∥₊) _ _),
  { calc ∑ i, c * cᵢ i * ∥l i∥₊
        = c * ∑ i, cᵢ i * ∥l i∥₊ : by simp only [mul_assoc, ← finset.mul_sum]
    ... = c * ∥l'∥₊ : by rw h2
    ... ≤ c * c' : mul_le_mul' le_rfl hl' },
  rintro i -,
  rw [mul_assoc, mul_left_comm, x.map_nsmul],
  exact pseudo_normed_group.nat_smul_mem_filtration (cᵢ i) _ _ (H i),
end

end

namespace polyhedral_lattice

variables (Λ : Type*) (r' : ℝ≥0) (M : Type*) [polyhedral_lattice Λ]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]

include r'

namespace add_monoid_hom

variables {Λ r' M} (c : ℝ≥0)

def incl (c : ℝ≥0) : filtration (Λ →+ M) c → Π l : Λ, filtration M (c * ∥l∥₊) :=
λ f l, ⟨f l, f.2 $ mem_filtration_nnnorm _⟩

@[simp] lemma coe_incl_apply (f : filtration (Λ →+ M) c) (l : Λ) :
  (incl c f l : M) = f l :=
rfl

variables (Λ r' M)

lemma incl_injective : function.injective (@incl Λ r' M _ _ c) :=
begin
  intros f g h,
  ext l,
  show (incl c f l : M) = incl c g l,
  rw h
end

instance : topological_space (filtration (Λ →+ M) c) :=
topological_space.induced (incl c) infer_instance

lemma incl_embedding : embedding (@incl Λ r' M _ _ c) :=
{ induced := rfl,
  inj := incl_injective Λ r' M c }

lemma incl_inducing : inducing (@incl Λ r' M _ _ c) := ⟨rfl⟩

lemma incl_continuous : continuous (@incl Λ r' M _ _ c) :=
(incl_inducing _ _ _ _).continuous

instance : t2_space (filtration (Λ →+ M) c) :=
(incl_embedding Λ r' M c).t2_space

instance : totally_disconnected_space (filtration (Λ →+ M) c) :=
{ is_totally_disconnected_univ := (incl_embedding Λ r' M c).is_totally_disconnected $
    is_totally_disconnected_of_totally_disconnected_space _ }

lemma incl_range_eq :
  (set.range (@incl Λ r' M _ _ c)) =
    ⋂ l₁ l₂, {f | (cast_le (f (l₁ + l₂)) : filtration M (c * (∥l₁∥₊ + ∥l₂∥₊))) =
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
  comphaus_filtered_pseudo_normed_group

lemma incl_range_is_closed : (is_closed (set.range (@incl Λ r' M _ _ c))) :=
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
    rw ← (incl_inducing Λ r' M c).is_compact_iff,
    apply is_closed.is_compact,
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
    have step2 := (continuous_add' (c₁ * ∥l∥₊) (c₂ * ∥l∥₊)),
    have := step2.comp step1,
    refine (@continuous_cast_le _ _ _ _ (id _)).comp this,
    rw add_mul, exact ⟨le_rfl⟩
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
open comphaus_filtered_pseudo_normed_group
variables [fact (0 < r')]

def Tinv : comphaus_filtered_pseudo_normed_group_hom (Λ →+ M) (Λ →+ M) :=
comphaus_filtered_pseudo_normed_group_hom.mk' Tinv'
begin
  refine ⟨r'⁻¹, λ c, ⟨Tinv'_mem_filtration c, _⟩⟩,
  rw add_monoid_hom.continuous_iff,
  intro l,
  haveI : ∀ a, fact (a ≤ r' * (r'⁻¹ * a)) :=
    λ a, ⟨by simp [mul_inv_cancel_left₀ (ne_of_gt (fact.out _ : 0 < r'))]⟩,
  refine (@continuous_cast_le _ _ _ _ (id _)).comp
    ((@Tinv₀_continuous r' M _ (c * ∥l∥₊) (r'⁻¹ * (c * ∥l∥₊)) _).comp
    ((continuous_apply l).comp (add_monoid_hom.incl_continuous Λ r' M c))),
  rw mul_assoc, exact ⟨le_rfl⟩
end

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Λ →+ M) :=
{ Tinv := Tinv Λ r' M,
  Tinv_mem_filtration := Tinv'_mem_filtration,
  .. add_monoid_hom.profinitely_filtered_pseudo_normed_group Λ r' M }

@[simp] lemma Tinv_apply (x : Λ →+ M) (l : Λ) :
  (profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv x) l =
  profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv (x l) := rfl

end polyhedral_lattice
