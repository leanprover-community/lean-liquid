import pseudo_normed_group.system_of_complexes
import polyhedral_lattice.pseudo_normed_group
import Mbar.pseudo_normed_group

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.

variables (BD : breen_deligne.package)
variables (c' : ℕ → ℝ≥0)  -- implicit constants, chosen once and for all
                          -- see the sentence after that statement of Thm 9.5

namespace ProFiltPseuNormGrpWithTinv

universe variables u

def Hom {r' : ℝ≥0} (Λ : Type) (M : Type u)
  [normed_group Λ] [polyhedral_lattice Λ]
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  ProFiltPseuNormGrpWithTinv.{u} r' :=
of r' (Λ →+ M)

end ProFiltPseuNormGrpWithTinv

open ProFiltPseuNormGrpWithTinv

/-- Theorem 9.5 in [Analytic] -/
theorem thm95 [BD.suitable c']
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)] :
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∀ (Λ : Type) [normed_group Λ],​ ∀ [polyhedral_lattice Λ],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : NormedGroup) [normed_with_aut r V],
    ​(BD.system c' r V r' (Hom Λ (Mbar r' S))).is_bounded_exact k K m c₀ :=
sorry

noncomputable
def HomZ_iso (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)] (S : Type) [fintype S] :
  Hom ℤ (Mbar r' S) ≅ of r' (Mbar r' S) :=
{ hom :=
  { to_fun := λ (f : ℤ →+ Mbar r' S), f 1,
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
      suffices : n • x ∈ pseudo_normed_group.filtration (Mbar r' S) (n.nat_abs * c),
      { rw [← int.cast_add_hom'_apply, nnreal.coe_nat_abs, mul_comm] at this,
        exact (pseudo_normed_group.filtration_mono (mul_le_mul_left' hn c) this) },
      exact pseudo_normed_group.int_smul_mem_filtration n x c hx,
    end,
    continuous' := sorry,
    map_Tinv' := sorry },
  hom_inv_id' := by { ext (f : ℤ →+ Mbar r' S) : 2,
    calc int.cast_add_hom' (f 1) 1 = 1 • f 1 : rfl
    ... = f 1 : one_smul _ _ },
  inv_hom_id' := by { ext1 x,
    calc int.cast_add_hom' x 1 = 1 • x : rfl
    ... = x : one_smul _ _ } }
