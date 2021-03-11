import polyhedral_lattice.pseudo_normed_group
import pseudo_normed_group.category

import for_mathlib.add_monoid_hom
import for_mathlib.free_abelian_group -- for int.cast_add_hom', which should move
import Mbar.basic -- for nnreal.coe_nat_abs, which should move

noncomputable theory
universe variables u
open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.

variables (c' : ℕ → ℝ≥0)  -- implicit constants, chosen once and for all
                          -- see the sentence after that statement of Thm 9.5

namespace ProFiltPseuNormGrpWithTinv

open pseudo_normed_group profinitely_filtered_pseudo_normed_group_with_Tinv_hom
profinitely_filtered_pseudo_normed_group_with_Tinv (Tinv)

variables {r : ℝ≥0} {M₁ M₂ : Type u}
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r M₁]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r M₂]
variables {f : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r M₁ M₂}

/-- The isomorphism induced by a bijective `profinitely_filtered_pseudo_normed_group_with_Tinv_hom`
whose inverse is strict. -/
noncomputable
def iso_of_equiv_of_strict (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) :
  of r M₁ ≅ of r M₂ :=
{ hom := f,
  inv := inv_of_equiv_of_strict e he strict,
  hom_inv_id' := by { ext x, simp [inv_of_equiv_of_strict, he] },
  inv_hom_id' := by { ext x, simp [inv_of_equiv_of_strict, he] } }

@[simp]
lemma iso_of_equiv_of_strict.apply (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) (x : M₁) :
  (iso_of_equiv_of_strict e he strict).hom x = f x := rfl

@[simp]
lemma iso_of_equiv_of_strict_symm.apply (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) (x : M₂) :
  (iso_of_equiv_of_strict e he strict).symm.hom x = e.symm x := rfl

def Hom {r : ℝ≥0} (Λ : Type) (M : Type u) [normed_group Λ] [polyhedral_lattice Λ]
  [profinitely_filtered_pseudo_normed_group_with_Tinv r M] :
  ProFiltPseuNormGrpWithTinv.{u} r :=
of r (Λ →+ M)

/-- The morphism `M ⟶ Hom ℤ M` for `M` a `profinitely_filtered_pseudo_normed_group_with_Tinv`. -/
noncomputable
def HomZ_map {r : ℝ≥0} [fact (0 < r)] [fact (r ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r M] :
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom r M (Hom ℤ M) :=
{ to_fun := int.cast_add_hom',
  map_zero' := by { ext1, simp only [pi.zero_apply, add_monoid_hom.coe_zero, smul_zero, int.cast_add_hom'_apply] },
  map_add' := by { intros, ext1, simp only [smul_add, add_monoid_hom.coe_add, add_left_inj,
    pi.add_apply, one_smul, int.cast_add_hom'_apply] },
  strict' := λ c x hx c₁ n hn,
  begin
    rw [normed_group.mem_filtration_iff] at hn,
    suffices : n • x ∈ pseudo_normed_group.filtration M (n.nat_abs * c),
    { rw [← int.cast_add_hom'_apply, nnreal.coe_nat_abs, mul_comm] at this,
      exact (pseudo_normed_group.filtration_mono (mul_le_mul_left' hn c) this) },
    exact pseudo_normed_group.int_smul_mem_filtration n x c hx,
  end,
  continuous' := λ c,
  begin
    rw [polyhedral_lattice.add_monoid_hom.continuous_iff],
    intro n,
    exact pfpng_ctu_smul_int M n _ (λ x, rfl),
  end,
  map_Tinv' := λ x,
  begin
    refine add_monoid_hom.ext (λ n, _),
    have h : (Tinv (int.cast_add_hom' x)) n = Tinv (int.cast_add_hom' x n) := rfl,
    simp only [h, int.cast_add_hom'_apply, profinitely_filtered_pseudo_normed_group_hom.map_gsmul],
  end }

/-- `HomZ_map` as an equiv. -/
@[simps]
def HomZ_map_equiv {r : ℝ≥0} [fact (0 < r)] [fact (r ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r M] :
  M ≃+ Hom ℤ M :=
{ inv_fun := λ (f : ℤ →+ M), f 1,
  left_inv := λ x, one_smul _ _,
  right_inv := λ f, by { ext, exact one_smul _ _ },
  ..HomZ_map M }

/-- The inverse of `HomZ_map` is strict. -/
lemma HomZ_map_inverse_strict {r : ℝ≥0} [fact (0 < r)] [fact (r ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r M] :
  ∀ c f, f ∈ filtration ((Hom ℤ M)) c → (HomZ_map_equiv M).symm f ∈ filtration M c :=
λ c f hf, by simpa [mul_one] using hf int.one_mem_filtration

/-- The isomorphism `Hom ℤ M ≅ M` for `M` a `profinitely_filtered_pseudo_normed_group_with_Tinv`. -/
noncomputable
def HomZ_iso {r : ℝ≥0} [fact (0 < r)] [fact (r ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r M] :
  Hom ℤ M ≅ of r M :=
(iso_of_equiv_of_strict (HomZ_map_equiv M) (λ x, rfl) (HomZ_map_inverse_strict M)).symm


end ProFiltPseuNormGrpWithTinv
