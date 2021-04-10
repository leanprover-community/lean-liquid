import polyhedral_lattice.Hom
import Mbar.pseudo_normed_group

import normed_spectral

import thm95.double_complex
import thm95.constants

noncomputable theory

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.


open polyhedral_lattice opposite

/- === Warning: with `BD.suitable` the rows are not admissible, we need `BD.very_suitable` === -/

open thm95.universal_constants system_of_double_complexes
open ProFiltPseuNormGrpWithTinv (of)

section

variables (BD : breen_deligne.data)
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : NormedGroup) [normed_with_aut r V]
variables (c_ : ℕ → ℝ≥0) [BD.very_suitable r r' c_]
variables (M : ProFiltPseuNormGrpWithTinv r')
variables (m : ℕ)
variables (Λ : PolyhedralLattice.{0})

include BD c_ r r' M V

def thm95.IH (m : ℕ) : Prop := ∀ Λ : PolyhedralLattice.{0},
  ​((BD.system c_ r V r').obj (op $ Hom Λ M)).is_weak_bounded_exact (k c_ m) (K BD c_ r r' m) m (c₀ Λ)

omit BD c_ r r' M V

lemma NSC_row_exact (IH : ∀ m' < m, thm95.IH BD r r' V c_ M m')
  (h0m : 0 < m) (i : ℕ) (hi : i ≤ m + 1) :
  ((thm95.double_complex BD c_ r r' V Λ M (N c_ r r' m)).row i).is_weak_bounded_exact
    (k₁ m) (K₁ m) (m - 1) (c₀ Λ) :=
begin
  have hm' : m - 1 < m := nat.pred_lt h0m.ne',
  rcases i with (i|i|i),
  { rw thm95.double_complex.row_zero,
    refine (IH (m-1) hm' Λ).of_le BD.system_admissible _ _ le_rfl ⟨le_rfl⟩,
    all_goals { apply_instance } },
  { rw thm95.double_complex.row_one,
    refine (IH (m-1) hm' _).of_le BD.system_admissible _ _ le_rfl _,
    swap 3,
    { /- turn this into an instance somewhere,
         we need to make the definition of `c₀` depend on `m` -/ sorry },
    all_goals { apply_instance } },
  { rw thm95.double_complex.row,
    apply system_of_complexes.rescale_is_weak_bounded_exact,
    refine (IH (m-1) hm' _).of_le BD.system_admissible _ _ le_rfl _,
    swap 3,
    { /- turn this into an instance somewhere,
         we need to make the definition of `c₀` depend on `m` -/ sorry },
    all_goals { apply_instance } }
end

def NSC_htpy :
  normed_spectral_homotopy
    ((thm95.double_complex BD c_ r r' V Λ M (N c_ r r' m)).row 0)
    ((thm95.double_complex BD c_ r r' V Λ M (N c_ r r' m)).row 1)
    ((thm95.double_complex BD c_ r r' V Λ M (N c_ r r' m)).row_map 0 1)
      m (k' c_ m) (ε m) (c₀ Λ) (H BD c_ r r' m) :=
{ h := sorry,
  h_bound_by := sorry,
  δ := sorry,
  hδ := sorry,
  δ_bound_by := sorry }

def NSC (IH : ∀ m' < m, thm95.IH BD r r' V c_ M m') :
  normed_spectral_conditions (thm95.double_complex BD c_ r r' V Λ M (N c_ r r' m)) m
    (k₁ m) (K₁ m) (k' c_ m) (ε m) (c₀ Λ) (H BD c_ r r' m) :=
{ row_exact := NSC_row_exact _ _ _ _ _ _ _ _ IH,
  col_exact := sorry,
  htpy := NSC_htpy BD r r' V c_ M m Λ,
  admissible := thm95.double_complex_admissible _ }

include BD c_ r r' M V m

/-- Theorem 9.5 in [Analytic] -/
theorem thm95 : ∀ (Λ : PolyhedralLattice.{0}) (S : Type) [fintype S]
  (V : NormedGroup) [normed_with_aut r V],
  ​((BD.system c_ r V r').obj (op $ Hom Λ (Mbar r' S))).is_weak_bounded_exact
    (k c_ m) (K BD c_ r r' m) m (c₀ Λ) :=
begin
  apply nat.strong_induction_on m; clear m,
  introsI m IH Λ S _S_fin V _V_r,
  let cond := NSC BD r r' V c_ (of r' $ Mbar r' S) m Λ _,
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
theorem thm95' (BD : breen_deligne.data)
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
  (c_ : ℕ → ℝ≥0) [BD.very_suitable r r' c_] :
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∀ (Λ : Type) [polyhedral_lattice Λ],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : NormedGroup) [normed_with_aut r V],
    by exactI system_of_complexes.is_bounded_exact
    (​(BD.system c_ r V r').obj (op $ Hom Λ (Mbar r' S))) k K m c₀ :=
begin
  intro m,
  apply nat.strong_induction_on m; clear m,
  intros m IH,
  sorry
end
