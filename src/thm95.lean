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
    ​(BD.system c' r V r' (Hom Λ (Mbar r' S))).is_bdd_exact_for_bdd_degree_above_idx k K m c₀ :=
sorry
