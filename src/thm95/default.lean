import polyhedral_lattice.Hom
import Mbar.pseudo_normed_group

import normed_spectral

import thm95.double_complex
import thm95.constants

noncomputable theory

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.

variables (BD : breen_deligne.package)
variables (c' : ℕ → ℝ≥0)  -- implicit constants, chosen once and for all
                          -- see the sentence after the statement of Thm 9.5

open polyhedral_lattice

/- === Warning: with `BD.suitable` the rows are not admissible, we need `BD.very_suitable` === -/

open thm95.universal_constants system_of_double_complexes
open ProFiltPseuNormGrpWithTinv (of)

section

variables [BD.suitable c']
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (M : ProFiltPseuNormGrpWithTinv r') (V : NormedGroup) [normed_with_aut r V]
variables (m : ℕ)
variables (Λ : PolyhedralLattice.{0})

include BD c' r r' M V

def thm95.IH (m : ℕ) : Prop := ∀ Λ : PolyhedralLattice.{0},
  ​(BD.system c' r V r' (Hom Λ M)).is_weak_bounded_exact (k c' m) (K BD c' r r' m) m (c₀ Λ)

omit BD c' r r' M V

lemma NSC_row_exact (IH : ∀ m' < m, thm95.IH BD c' r r' M V m')
  (h0m : 0 < m) (i : ℕ) (hi : i ≤ m + 1) :
  ((thm95.double_complex BD c' r r' V Λ M (N c' r r' m)).row i).is_weak_bounded_exact
    (k₁ m) (K₁ m) (m - 1) (c₀ Λ) :=
begin
  have hm' : m - 1 < m := nat.pred_lt h0m.ne',
  rcases i with (i|i|i),
  { rw thm95.double_complex.row_zero,
    refine (IH (m-1) hm' Λ).of_le thm95.system_admissible _ _ le_rfl le_rfl,
    all_goals { apply_instance } },
  { rw thm95.double_complex.row_one,
    refine (IH (m-1) hm'
      (PolyhedralLattice.of $ conerve.obj (Λ.diagonal_embedding (N c' r r' m)) 1)).of_le
      thm95.system_admissible _ _ le_rfl _,
    swap 3, { /- turn this into an instance somewhere -/ sorry },
    all_goals { apply_instance } },
  { rw thm95.double_complex.row,
    apply system_of_complexes.rescale_is_weak_bounded_exact,
    refine (IH (m-1) hm'
      (PolyhedralLattice.of $ conerve.obj (Λ.diagonal_embedding (N c' r r' m)) (i + 2))).of_le
      thm95.system_admissible _ _ le_rfl _,
    swap 3, { /- turn this into an instance somewhere -/ sorry },
    all_goals { apply_instance } }
end

def NSC (IH : ∀ m' < m, thm95.IH BD c' r r' M V m') :
  normed_spectral_conditions (thm95.double_complex BD c' r r' V Λ M (N c' r r' m)) m
    (k₁ m) (K₁ m) (k' c' m) (ε m) (c₀ Λ) (H BD c' r r' m) :=
{ col_exact := sorry,
  row_exact := NSC_row_exact _ _ _ _ _ _ _ _ IH,
  h := sorry,
  h_bound_by := sorry,
  δ := sorry,
  hδ := sorry,
  δ_bound_by := sorry,
  admissible := thm95.double_complex_admissible _ }

include BD c' r r' M V m

/-- Theorem 9.5 in [Analytic] -/
theorem thm95 : ∀ (Λ : PolyhedralLattice.{0}) (S : Type) [fintype S]
  (V : NormedGroup) [normed_with_aut r V],
  ​(BD.system c' r V r' (Hom Λ (Mbar r' S))).is_weak_bounded_exact
    (k c' m) (K BD c' r r' m) m (c₀ Λ) :=
begin
  apply nat.strong_induction_on m; clear m,
  introsI m IH Λ S _S_fin V _V_r,
  let cond := NSC BD c' r r' (of r' $ Mbar r' S) V m Λ _,
  swap,
  { introsI m' hm' Λ,
    apply IH, assumption },
  exact normed_spectral cond
end

end



/- ===
Once we have determined the final shape of the statement,
we can update the proof `thm95' → first_target`, and then delete the theorem below.
Now I just want flexibility in changing `thm95`
and not be troubled with fixing the proof of the implication.
=== -/

/-- Theorem 9.5 in [Analytic] -/
theorem thm95' [BD.suitable c']
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)] :
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∀ (Λ : Type) [polyhedral_lattice Λ],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : NormedGroup) [normed_with_aut r V],
    ​(BD.system c' r V r' (Hom Λ (Mbar r' S))).is_bounded_exact k K m c₀ :=
begin
  intro m,
  apply nat.strong_induction_on m; clear m,
  intros m IH,
  sorry
end
