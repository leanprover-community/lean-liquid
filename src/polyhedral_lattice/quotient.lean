import analysis.normed.group.quotient
import linear_algebra.free_module.pid
import linear_algebra.free_module.finite.basic

import polyhedral_lattice.topology


/-!
# Quotients of polyhedral lattices
-/

noncomputable theory

open_locale big_operators

namespace polyhedral_lattice

variables {Λ : Type*} [polyhedral_lattice Λ] (L : add_subgroup Λ)

instance : is_closed (L : set Λ) :=
is_closed_discrete _

instance : normed_group (Λ ⧸ L) :=
add_subgroup.normed_group_quotient _

lemma π_apply_eq_zero_iff (x) : L.normed_mk x = 0 ↔ x ∈ L :=
quotient_add_group.eq_zero_iff _

lemma π_is_quotient : L.normed_mk.is_quotient :=
normed_group_hom.is_quotient_quotient _

instance [H : fact L.saturated] : no_zero_smul_divisors ℤ (Λ ⧸ L) :=
{ eq_zero_or_eq_zero_of_smul_eq_zero :=
  begin
    intros n x h,
    obtain ⟨x, rfl⟩ : ∃ y, L.normed_mk y = x := quotient.surjective_quotient_mk' x,
    have : L.normed_mk (n • x) = n • L.normed_mk x := L.normed_mk.to_add_monoid_hom.map_zsmul x n,
    simp only [← this, π_apply_eq_zero_iff] at h ⊢,
    exact add_subgroup.saturated_iff_zsmul.mp H.1 _ _ h,
  end }

instance quotient_finite : module.finite ℤ (Λ ⧸ L) :=
begin
  apply module.finite.of_surjective (L.normed_mk).to_add_monoid_hom.to_int_linear_map,
  exact quotient.surjective_quotient_mk'
end

instance quotient_free [H : fact L.saturated] : module.free ℤ (Λ ⧸ L) :=
begin
  let φ := L.normed_mk.to_add_monoid_hom.to_int_linear_map,
  suffices : submodule.span ℤ (set.range (φ ∘ (module.free.choose_basis ℤ Λ))) = ⊤,
  { obtain ⟨n, b⟩ := module.free_of_finite_type_torsion_free this,
    exact module.free.of_basis b, },
  rw [set.range_comp, ← submodule.map_span, basis.span_eq,
    submodule.map_top, linear_map.range_eq_top],
  exact quotient.surjective_quotient_mk'
end

open pseudo_normed_group

lemma norm_lift (y : Λ ⧸ L) :
  ∃ x, L.normed_mk x = y ∧ ∥x∥ = ∥y∥ :=
begin
  have hq : L.normed_mk.is_quotient := normed_group_hom.is_quotient_quotient _,
  let s := λ ε, {x | L.normed_mk x = y ∧ ∥x∥₊ ≤ ∥y∥₊ + ε },
  have hs : ∀ ε, (s ε).finite,
  { intro ε,
    apply (filtration_finite Λ (∥y∥₊ + ε)).subset,
    rintro x ⟨h1, h2⟩,
    simpa only [semi_normed_group.mem_filtration_iff] using h2 },
  let t := λ ε, (hs ε).to_finset,
  have ht : ∀ ε, 0 < ε → (t ε).nonempty,
  { intros ε hε,
    obtain ⟨x, h1, h2⟩ := hq.norm_lift hε y,
    refine ⟨x, _⟩, simp only [set.finite.mem_to_finset], exact ⟨h1, h2.le⟩ },
  let r := ((t 1).image nnnorm).min' ((ht _ zero_lt_one).image _),
  have aux := finset.min'_mem ((t 1).image nnnorm) ((ht _ zero_lt_one).image _),
  simp only [finset.mem_image] at aux,
  obtain ⟨x, hx, H⟩ := aux,
  simp only [set.finite.mem_to_finset, set.mem_set_of_eq] at hx,
  suffices hr : r = ∥y∥₊,
  { refine ⟨x, hx.1, _⟩,
    simp only [← coe_nnnorm, nnreal.coe_injective.eq_iff],
    exact H.trans hr },
  refine ((lt_or_eq_of_le _).resolve_left _).symm,
  { rw ← hx.1, exact (hq.norm_le x).trans H.le },
  { intro hyr,
    let ε := (r - ∥y∥₊) / 2,
    have hε' : (ε : ℝ) = (r - ∥y∥₊) / 2,
    { dsimp only [ε], rw [nnreal.coe_div, nnreal.coe_sub hyr.le, nnreal.coe_bit0, nnreal.coe_one] },
    have hε : 0 < ε,
    { rw [← nnreal.coe_lt_coe, nnreal.coe_zero, hε'],
      exact div_pos (sub_pos.mpr $ nnreal.coe_lt_coe.mpr hyr) zero_lt_two },
    have key : ∥y∥₊ + ε < r,
    { rw [← nnreal.coe_lt_coe, nnreal.coe_add, hε'],
      exact add_sub_div_two_lt (nnreal.coe_lt_coe.mpr hyr), },
    refine not_le_of_lt key _,
    obtain ⟨x₀, hx₀⟩ := ht ε hε,
    simp only [exists_prop, set.finite.mem_to_finset, finset.mem_image, set.mem_set_of_eq] at hx₀,
    refine (finset.min'_le _ _ _).trans hx₀.2,
    simp only [exists_prop, set.finite.mem_to_finset, finset.mem_image, set.mem_set_of_eq],
    exact ⟨x₀, ⟨hx₀.1, (hx₀.2.trans key.le).trans (H.ge.trans hx.2)⟩, rfl⟩, }
end

instance [H : fact L.saturated] : polyhedral_lattice (Λ ⧸ L) :=
{ polyhedral' :=
  begin
    obtain ⟨ι, _inst_ι, l, hl, hl'⟩ := polyhedral_lattice.polyhedral Λ, resetI,
    refine ⟨ι, _inst_ι, (λ i, L.normed_mk (l i)), _⟩,
    intros y,
    obtain ⟨x, rfl, hx⟩ := norm_lift _ y,
    obtain ⟨c, H1, H2⟩ := hl x,
    have key : _ := _,
    refine ⟨c, key, _⟩, swap,
    { show L.normed_mk x = _,
      rw [H1, normed_group_hom.map_sum, fintype.sum_congr],
      intro, exact L.normed_mk.to_add_monoid_hom.map_nsmul _ _ },
    { apply le_antisymm,
      { rw key,
        exact (norm_sum_le _ _).trans (finset.sum_le_sum $ λ i hi, norm_nsmul_le _ _) },
      { simp only [← hx, H2],
        apply finset.sum_le_sum,
        rintro i -,
        have hq : L.normed_mk.is_quotient := normed_group_hom.is_quotient_quotient _,
        exact mul_le_mul le_rfl (hq.norm_le _) (norm_nonneg _) (nat.cast_nonneg _) } },
  end }

end polyhedral_lattice
