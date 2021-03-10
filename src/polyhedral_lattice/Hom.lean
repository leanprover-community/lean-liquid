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

variables {r : ℝ≥0} {M₁ M₂ : Type u}
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r M₁]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r M₂]
variables (f : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r M₁ M₂)

/-- The isomorphism induced by a bijective `profinitely_filtered_pseudo_normed_group_with_Tinv_hom`
whose inverse is strict. -/
noncomputable
def equiv.of_bijective (hf : function.bijective f)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → (equiv.of_bijective f hf).symm x ∈ filtration M₁ c) :
  of r M₁ ≅ of r M₂ :=
{ hom := f,
  inv := profinitely_filtered_pseudo_normed_group_with_Tinv_hom.inv_of_bijective hf strict,
  hom_inv_id' := by { ext x, simp [inv_of_bijective.apply x hf strict] },
  inv_hom_id' := by { ext x, simp [inv_of_bijective_symm.apply x hf strict] } }

def Hom {r' : ℝ≥0} (Λ : Type) (M : Type u)
  [normed_group Λ] [polyhedral_lattice Λ]
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  ProFiltPseuNormGrpWithTinv.{u} r' :=
of r' (Λ →+ M)

@[simp]
lemma equiv.of_bijective.apply (x : M₁) (hf : function.bijective f)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → (_root_.equiv.of_bijective f hf).symm x ∈ filtration M₁ c) :
  (equiv.of_bijective f hf strict).hom x = f x := rfl

@[simp]
lemma equiv.of_bijective_symm.apply (x : M₂) (hf : function.bijective f)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → (_root_.equiv.of_bijective f hf).symm x ∈ filtration M₁ c) :
  (equiv.of_bijective f hf strict).symm.hom x = (_root_.equiv.of_bijective f hf).symm x := rfl

/-- The morphism `M ⟶ Hom ℤ M` for `M` a `profinitely_filtered_pseudo_normed_group_with_Tinv`. -/
noncomputable
def HomZ_map (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M (Hom ℤ M) :=
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
    refine pfpng_ctu_smul_int M n _ _,
    intro x,
    refl
  end,
  map_Tinv' := λ x,
  begin
    refine add_monoid_hom.ext (λ n, _),
    have h : (profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv (int.cast_add_hom' x)) n =
      profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv (int.cast_add_hom' x n) := rfl,
    simp only [h, int.cast_add_hom'_apply, profinitely_filtered_pseudo_normed_group_hom.map_gsmul],
  end }

/-- The inverse of `HomZ_map` as function. -/
noncomputable
def HomZ_map_inv (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  (Hom ℤ M) → M := λ (f : ℤ →+ M), f 1

lemma left_inv_HomZ_map (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  function.left_inverse (HomZ_map_inv r' M) (HomZ_map r' M) :=
begin
  intro x,
  calc int.cast_add_hom' x 1 = 1 • x : rfl
    ... = x : one_smul _ _
end

lemma right_inv_HomZ_map (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  function.right_inverse (HomZ_map_inv r' M) (HomZ_map r' M) :=
begin
  intro f,
  ext,
  calc int.cast_add_hom' (f.to_fun 1) 1 = 1 • f.to_fun 1 : rfl
  ... = f.to_fun 1 : one_smul _ _
end

/-- `HomZ_map` is bijective. -/
lemma HomZ_map_bijective (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] : function.bijective (HomZ_map r' M) :=
begin
  rw [function.bijective_iff_has_inverse],
  refine ⟨λ (f : ℤ →+ M), f 1, left_inv_HomZ_map r' M, right_inv_HomZ_map r' M⟩
end

/-- The inverse of `HomZ_map` is strict. -/
lemma HomZ_map_inverse_strict (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  ∀ c f, f ∈ filtration ((Hom ℤ M)) c → (_root_.equiv.of_bijective (HomZ_map r' M)
  (HomZ_map_bijective r' M)).symm f ∈ filtration M c :=
begin
  intros c f hf,
  have h : (_root_.equiv.of_bijective (HomZ_map r' M) ((HomZ_map_bijective r' M))).symm f =
    (HomZ_map_inv r' M) f,
    { apply function.bijective.injective (HomZ_map_bijective r' M),
      rw [← function.comp_app (HomZ_map r' M), right_inv_HomZ_map, function.comp_app (HomZ_map r' M)],
      rw [equiv.of_bijective_apply_symm_apply (HomZ_map r' M) (HomZ_map_bijective r' M) _] },
  simp [h, HomZ_map_inv],
  simpa [mul_one] using hf int.one_mem_filtration
end

/-- The isomorphism `Hom ℤ M ≅ M` for `M` a `profinitely_filtered_pseudo_normed_group_with_Tinv`. -/
noncomputable
def HomZ_iso (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  Hom ℤ M ≅ of r' M :=
(equiv.of_bijective (HomZ_map r' M) (HomZ_map_bijective r' M) (HomZ_map_inverse_strict r' M)).symm


end ProFiltPseuNormGrpWithTinv
