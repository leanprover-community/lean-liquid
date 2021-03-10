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

def Hom {r' : ℝ≥0} (Λ : Type) (M : Type u)
  [normed_group Λ] [polyhedral_lattice Λ]
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  ProFiltPseuNormGrpWithTinv.{u} r' :=
of r' (Λ →+ M)

noncomputable
def HomZ_iso (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (M : Type)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  Hom ℤ M ≅ of r' M :=
{ hom :=
  { to_fun := λ (f : ℤ →+ M), f 1,
    map_zero' := by simp only [pi.zero_apply, eq_self_iff_true, add_monoid_hom.coe_zero],
    map_add' := by { intros, simp only [add_monoid_hom.coe_add, add_left_inj, pi.add_apply] },
    strict' := λ c f hf, by simpa only [mul_one] using hf int.one_mem_filtration,
    continuous' := sorry,
    map_Tinv' := λ f, rfl },
  inv :=
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
    end },
  hom_inv_id' := by { ext (f : ℤ →+ M) : 2,
    calc int.cast_add_hom' (f 1) 1 = 1 • f 1 : rfl
    ... = f 1 : one_smul _ _ },
  inv_hom_id' := by { ext1 x,
    calc int.cast_add_hom' x 1 = 1 • x : rfl
    ... = x : one_smul _ _ } }

end ProFiltPseuNormGrpWithTinv
