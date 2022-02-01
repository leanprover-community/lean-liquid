import breen_deligne.constants
import system_of_complexes.completion
import thm95.homotopy
import thm95.col_exact
import combinatorial_lemma.profinite


noncomputable theory

universe variable u

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.


open polyhedral_lattice opposite
open thm95.universal_constants system_of_double_complexes category_theory breen_deligne
open ProFiltPseuNormGrpWithTinv (of)

section

variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]
variables (BD : package)
variables (V : SemiNormedGroup.{u}) [normed_with_aut r V]
variables (κ κ' : ℕ → ℝ≥0) [BD.data.very_suitable r r' κ] [package.adept BD κ κ']
variables (M : ProFiltPseuNormGrpWithTinv.{u} r')
variables (m : ℕ)
variables (Λ : PolyhedralLattice.{u})

include BD κ κ' r r' M V

def thm95.IH (m : ℕ) : Prop := ∀ Λ : PolyhedralLattice.{u},
  ​((BD.data.system κ r V r').obj (op $ Hom Λ M)).is_weak_bounded_exact
    (k κ' m) (K r r' BD κ' m) m (c₀ r r' BD κ κ' m Λ)

omit BD κ κ' r r' M V

lemma NSC_row_exact (IH : ∀ m' < m, thm95.IH r r' BD V κ κ' M m')
  (h0m : 0 < m) (i : ℕ) (hi : i ≤ m + 1) :
  ((thm95.double_complex BD.data κ r r' V Λ M (N r r' BD κ' m)).row i).is_weak_bounded_exact
    (k₁ κ' m) (K₁ r r' BD κ' m) (m - 1) (c₀ r r' BD κ κ' m Λ) :=
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

def NSC (IH : ∀ m' < m, thm95.IH r r' BD V κ κ' M m')
  [pseudo_normed_group.splittable (Λ →+ M) (N r r' BD κ' m) (lem98.d Λ (N r r' BD κ' m))] :
  normed_spectral_conditions (thm95.double_complex BD.data κ r r' V Λ M (N r r' BD κ' m)) m
    (k₁ κ' m) (K₁ r r' BD κ' m) (k' κ' m) (ε r r' BD κ' m) (c₀ r r' BD κ κ' m Λ) (H r r' BD κ' m) :=
{ row_exact := NSC_row_exact _ _ _ _ _ _ _ _ _ IH,
  col_exact :=
  begin
    let N := N r r' BD κ' m,
    intros j hj,
    refine thm95.col_exact BD.data κ r r' V Λ M N j (lem98.d Λ N) (k₁_sqrt κ' m) m _ _
      (k₁ κ' m) (K₁ r r' BD κ' m) (le_of_eq _) _ _ (c₀ r r' BD κ κ' m Λ) ⟨le_rfl⟩ infer_instance ⟨le_rfl⟩,
    { apply c₀_spec, assumption', },
    { ext, delta k₁_sqrt, dsimp, simp only [real.mul_self_sqrt, nnreal.zero_le_coe], },
    { apply K₁_spec }
  end,
  htpy := NSC_htpy BD r r' V κ κ' M m Λ,
  admissible := thm95.double_complex_admissible _ }

include BD κ κ' r r' m

/-- A variant of Theorem 9.5 in [Analytic] using weak bounded exactness. -/
theorem thm95' : ∀ (Λ : PolyhedralLattice.{u}) (S : Type u) [fintype S]
  (V : SemiNormedGroup.{u}) [normed_with_aut r V],
  ​((BD.data.system κ r V r').obj (op $ Hom Λ (Mbar r' S))).is_weak_bounded_exact
    (k κ' m) (K r r' BD κ' m) m (c₀ r r' BD κ κ' m Λ) :=
begin
  apply nat.strong_induction_on m; clear m,
  introsI m IH Λ S _S_fin V _V_r,
  haveI : pseudo_normed_group.splittable
    (Λ →+ (of r' (Mbar r' S))) (N r r' BD κ' m) (lem98.d Λ (N r r' BD κ' m)) :=
    lem98_finite Λ S (N r r' BD κ' m),
  let cond := NSC.{u} r r' BD V κ κ' (of r' $ Mbar r' S) m Λ _,
  swap,
  { introsI m' hm' Λ,
    apply IH, assumption },
  exact normed_spectral cond
end

set_option pp.universes true

/-- A variant of Theorem 9.5 in [Analytic] using weak bounded exactness. -/
theorem thm95'.profinite : ∀ (Λ : PolyhedralLattice.{u}) (S : Profinite.{u})
  (V : SemiNormedGroup.{u}) [normed_with_aut r V],
  ​((BD.data.system κ r V r').obj (op $ Hom Λ ((Mbar.functor.{u u} r').obj S))).is_weak_bounded_exact
    (k κ' m) (K r r' BD κ' m) m (c₀ r r' BD κ κ' m Λ) :=
begin
  apply nat.strong_induction_on m; clear m,
  introsI m IH Λ S V _V_r,
  haveI : pseudo_normed_group.splittable
    (Λ →+ (of r' ((Mbar.functor.{u u} r').obj S))) (N r r' BD κ' m) (lem98.d Λ (N r r' BD κ' m)) :=
    lem98.main r' Λ S (N r r' BD κ' m),
  let cond := NSC.{u} r r' BD V κ κ' (of r' $ (Mbar.functor.{u u} r').obj S) m Λ _,
  swap,
  { introsI m' hm' Λ,
    apply IH, assumption },
  exact normed_spectral cond
end

omit BD κ κ' r r' m

/-- Theorem 9.5 in [Analytic] -/
theorem thm95 (Λ : PolyhedralLattice.{u}) (S : Type u) [fintype S]
  (V : SemiNormedGroup.{u}) [normed_with_aut r V] :
  ((BD.data.system κ r V r').obj (op $ Hom Λ (Mbar r' S))).is_bounded_exact
    (k κ' m ^ 2) (K r r' BD κ' m + 1) m (c₀ r r' BD κ κ' m Λ) :=
begin
  refine system_of_complexes.is_weak_bounded_exact.strong_of_complete
    _ (thm95' r r' BD κ κ' m Λ S V) _ 1 zero_lt_one,
  apply data.system_admissible
end

/-- Theorem 9.5 in [Analytic] -/
theorem thm95.profinite (Λ : PolyhedralLattice.{u}) (S : Profinite.{u})
  (V : SemiNormedGroup.{u}) [normed_with_aut r V] :
  ((BD.data.system κ r V r').obj (op $ Hom Λ ((Mbar.functor.{u u} r').obj S))).is_bounded_exact
    (k κ' m ^ 2) (K r r' BD κ' m + 1) m (c₀ r r' BD κ κ' m Λ) :=
begin
  refine system_of_complexes.is_weak_bounded_exact.strong_of_complete
    _ (thm95'.profinite r r' BD κ κ' m Λ S V) _ 1 zero_lt_one,
  apply data.system_admissible
end

end



/- ===
Once we have determined the final shape of the statement,
we can update the proof `thm95' → first_target`, and then delete the theorem below.
Now I just want flexibility in changing `thm95`
and not be troubled with fixing the proof of the implication.
=== -/

/-- Theorem 9.5 in [Analytic] -/
theorem thm95'' (BD : package)
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]
  (κ : ℕ → ℝ≥0) [BD.data.very_suitable r r' κ] [∀ (i : ℕ), fact (0 < κ i)] :
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) (hk : fact (1 ≤ k)),
  ∀ (Λ : Type u) [polyhedral_lattice Λ],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type u) [fintype S],
  ∀ (V : SemiNormedGroup.{u}) [normed_with_aut r V],
    by exactI system_of_complexes.is_weak_bounded_exact
    (​(BD.data.system κ r V r').obj (op $ Hom Λ (Mbar r' S))) k K m c₀ :=
begin
  intro m,
  let κ' := package.κ' BD κ,
  haveI _inst_κ' : package.adept BD κ κ' := package.κ'_adept BD κ,
  refine ⟨(k κ' m), (K r r' BD κ' m), infer_instance, λ Λ _inst_Λ, _⟩,
  refine ⟨c₀ r r' BD κ κ' m (@PolyhedralLattice.of Λ _inst_Λ), λ S _inst_S V _inst_V, _⟩,
  apply thm95'
end

/-- Theorem 9.5 in [Analytic] -/
theorem thm95''.profinite (BD : package)
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]
  (κ : ℕ → ℝ≥0) [BD.data.very_suitable r r' κ] [∀ (i : ℕ), fact (0 < κ i)] :
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) (hk : fact (1 ≤ k)),
  ∀ (Λ : Type u) [polyhedral_lattice Λ],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Profinite.{u}),
  ∀ (V : SemiNormedGroup.{u}) [normed_with_aut r V],
    by exactI system_of_complexes.is_weak_bounded_exact
    (​(BD.data.system κ r V r').obj (op $ Hom Λ ((Mbar.functor.{u u} r').obj S))) k K m c₀ :=
begin
  intro m,
  let κ' := package.κ' BD κ,
  haveI _inst_κ' : package.adept BD κ κ' := package.κ'_adept BD κ,
  refine ⟨(k κ' m), (K r r' BD κ' m), infer_instance, λ Λ _inst_Λ, _⟩,
  refine ⟨c₀ r r' BD κ κ' m (@PolyhedralLattice.of Λ _inst_Λ), λ S _inst_S V _inst_V, _⟩,
  apply thm95'.profinite
end
