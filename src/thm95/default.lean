import breen_deligne.constants
import thm95.homotopy
import thm95.col_exact

noncomputable theory

universe variable u

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.


open polyhedral_lattice opposite
open thm95.universal_constants system_of_double_complexes category_theory breen_deligne
open ProFiltPseuNormGrpWithTinv (of)

section

variables (BD : package)
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]
variables (V : SemiNormedGroup.{u}) [normed_with_aut r V]
variables (c_ c' : ℕ → ℝ≥0) [BD.data.very_suitable r r' c_] [package.adept BD c_ c']
variables (M : ProFiltPseuNormGrpWithTinv.{u} r')
variables (m : ℕ)
variables (Λ : PolyhedralLattice.{u})

include BD c_ c' r r' M V

def thm95.IH (m : ℕ) : Prop := ∀ Λ : PolyhedralLattice.{u},
  ​((BD.data.system c_ r V r').obj (op $ Hom Λ M)).is_weak_bounded_exact
    (k c' m) (K BD c' r r' m) m (c₀ BD r r' c_ c' m Λ)

omit BD c_ c' r r' M V

lemma NSC_row_exact (IH : ∀ m' < m, thm95.IH BD r r' V c_ c' M m')
  (h0m : 0 < m) (i : ℕ) (hi : i ≤ m + 1) :
  ((thm95.double_complex BD.data c_ r r' V Λ M (N BD c' r r' m)).row i).is_weak_bounded_exact
    (k₁ c' m) (K₁ BD c' r r' m) (m - 1) (c₀ BD r r' c_ c' m Λ) :=
begin
  haveI h0m_ : fact (0 < m) := ⟨h0m⟩,
  have hm' : m - 1 < m := nat.pred_lt h0m.ne',
  rcases i with (i|i|i),
  { rw thm95.double_complex.row_zero,
  have := (IH (m-1) hm' Λ),
    refine (IH (m-1) hm' Λ).of_le BD.data.system_admissible _ _ le_rfl _,
    swap 3,
    { apply c₀_mono, },
    all_goals { apply_instance } },
  { rw thm95.double_complex.row_one,
    refine (IH (m-1) hm' _).of_le BD.data.system_admissible _ _ le_rfl _,
    swap 3,
    { apply c₀_pred_le, exact h0m },
    all_goals { apply_instance } },
  { rw thm95.double_complex.row,
    apply system_of_complexes.rescale_is_weak_bounded_exact,
    refine (IH (m-1) hm' _).of_le BD.data.system_admissible _ _ le_rfl _,
    swap 3,
    { apply c₀_pred_le_of_le, exact hi },
    all_goals { apply_instance } }
end
.

def NSC (IH : ∀ m' < m, thm95.IH BD r r' V c_ c' M m')
  [pseudo_normed_group.splittable (Λ →+ M) (N BD c' r r' m) (lem98.d Λ (N BD c' r r' m))] :
  normed_spectral_conditions (thm95.double_complex BD.data c_ r r' V Λ M (N BD c' r r' m)) m
    (k₁ c' m) (K₁ BD c' r r' m) (k' c' m) (ε BD c' r r' m) (c₀ BD r r' c_ c' m Λ) (H BD c' r r' m) :=
{ row_exact := NSC_row_exact _ _ _ _ _ _ _ _ _ IH,
  col_exact :=
  begin
    let N := N BD c' r r' m,
    intros j hj,
    refine thm95.col_exact BD.data c_ r r' V Λ M N j (lem98.d Λ N) (k₁_sqrt c' m) m _ _
      (k₁ c' m) (K₁ BD c' r r' m) (le_of_eq _) _ _ (c₀ BD r r' c_ c' m Λ) ⟨le_rfl⟩ infer_instance ⟨le_rfl⟩,
    { apply c₀_spec _ _ _ _ _ _ BD, all_goals { assumption, }, },
    { ext, delta k₁_sqrt, dsimp, simp only [real.mul_self_sqrt, nnreal.zero_le_coe], },
    { apply K₁_spec }
  end,
  htpy := NSC_htpy BD r r' V c_ c' M m Λ,
  admissible := thm95.double_complex_admissible _ }

include BD c_ c' r r' M V m

/-- Theorem 9.5 in [Analytic] -/
theorem thm95 : ∀ (Λ : PolyhedralLattice.{0}) (S : Type) [fintype S]
  (V : SemiNormedGroup.{0}) [normed_with_aut r V],
  ​((BD.data.system c_ r V r').obj (op $ Hom Λ (Mbar r' S))).is_weak_bounded_exact
    (k c' m) (K BD c' r r' m) m (c₀ BD r r' c_ c' m Λ) :=
begin
  apply nat.strong_induction_on m; clear m,
  introsI m IH Λ S _S_fin V _V_r,
  haveI : pseudo_normed_group.splittable
    (Λ →+ (of r' (Mbar r' S))) (N BD c' r r' m) (lem98.d Λ (N BD c' r r' m)) :=
    lem98 Λ S (N BD c' r r' m),
  let cond := NSC.{0} BD r r' V c_ c' (of r' $ Mbar r' S) m Λ _,
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
theorem thm95' (BD : package)
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]
  (c_ : ℕ → ℝ≥0) [BD.data.very_suitable r r' c_] [∀ (i : ℕ), fact (0 < c_ i)] :
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∀ (Λ : Type) [polyhedral_lattice Λ],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : SemiNormedGroup.{0}) [normed_with_aut r V],
    by exactI system_of_complexes.is_weak_bounded_exact
    (​(BD.data.system c_ r V r').obj (op $ Hom Λ (Mbar r' S))) k K m c₀ :=
begin
  intro m,
  let c' := package.c' BD c_,
  haveI _inst_c' : package.adept BD c_ c' := package.c'_adept BD c_,
  refine ⟨(k c' m), (K BD c' r r' m), infer_instance, λ Λ _inst_Λ, _⟩,
  refine ⟨c₀ BD r r' c_ c' m (@PolyhedralLattice.of Λ _inst_Λ), λ S _inst_S V _inst_V, _⟩,
  apply @thm95 BD r r' _ _ _ _ _ V _inst_V c_ c' _ _ (@Hom _ _ Λ (@Mbar r' S _inst_S)  _inst_Λ _)
end
