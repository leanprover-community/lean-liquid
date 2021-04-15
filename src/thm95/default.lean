import polyhedral_lattice.Hom
import Mbar.pseudo_normed_group

import normed_spectral

import pseudo_normed_group.homotopy

import thm95.double_complex
import thm95.constants

noncomputable theory

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.


open polyhedral_lattice opposite

/- === Warning: with `BD.suitable` the rows are not admissible, we need `BD.very_suitable` === -/

open thm95.universal_constants system_of_double_complexes category_theory breen_deligne
open ProFiltPseuNormGrpWithTinv (of)

section

variables (BD : package)
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : NormedGroup) [normed_with_aut r V]
variables (c_ c' : ℕ → ℝ≥0) [BD.data.very_suitable r r' c_] [package.adept BD c_ c']
variables (M : ProFiltPseuNormGrpWithTinv r')
variables (m : ℕ)
variables (Λ : PolyhedralLattice.{0})

include BD c_ c' r r' M V

def thm95.IH (m : ℕ) : Prop := ∀ Λ : PolyhedralLattice.{0},
  ​((BD.data.system c_ r V r').obj (op $ Hom Λ M)).is_weak_bounded_exact
    (k c' m) (K BD c_ c' r r' m) m (c₀ Λ)

omit BD c_ c' r r' M V

lemma NSC_row_exact (IH : ∀ m' < m, thm95.IH BD r r' V c_ c' M m')
  (h0m : 0 < m) (i : ℕ) (hi : i ≤ m + 1) :
  ((thm95.double_complex BD.data c_ r r' V Λ M (N c_ c' r r' m)).row i).is_weak_bounded_exact
    (k₁ m) (K₁ m) (m - 1) (c₀ Λ) :=
begin
  have hm' : m - 1 < m := nat.pred_lt h0m.ne',
  rcases i with (i|i|i),
  { rw thm95.double_complex.row_zero,
    refine (IH (m-1) hm' Λ).of_le BD.data.system_admissible _ _ le_rfl ⟨le_rfl⟩,
    all_goals { apply_instance } },
  { rw thm95.double_complex.row_one,
    refine (IH (m-1) hm' _).of_le BD.data.system_admissible _ _ le_rfl _,
    swap 3,
    { /- turn this into an instance somewhere,
         we need to make the definition of `c₀` depend on `m` -/ sorry },
    all_goals { apply_instance } },
  { rw thm95.double_complex.row,
    apply system_of_complexes.rescale_is_weak_bounded_exact,
    refine (IH (m-1) hm' _).of_le BD.data.system_admissible _ _ le_rfl _,
    swap 3,
    { /- turn this into an instance somewhere,
         we need to make the definition of `c₀` depend on `m` -/ sorry },
    all_goals { apply_instance } }
end
.

def NSH_aux_type (N : ℕ) (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :=
normed_spectral_homotopy
  ((BD_system_map (BD.data.sum (2^N)) c_ (rescale_constants c_ (2^N)) r V).app M)
  m (k' c' m) (ε m) (c₀ Λ) (H BD c_ c' r r' m)

section

variables {BD r r' V c_ c' m}

lemma NSH_h_res' {c x : ℝ≥0} {q' : ℕ} (hqm : q' ≤ m+1) :
  c * (c' q' * x) ≤ k' c' m * c * x :=
calc c * (c' q' * x)
    = c' q' * (c * x) : mul_left_comm _ _ _
... ≤ k' c' m * (c * x) : mul_le_mul' (c'_le_k' _ _ hqm) le_rfl
... = k' c' m * c * x : (mul_assoc _ _ _).symm

def NSH_h_res {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (c : ℝ≥0) {q' : ℕ} (hqm : q' ≤ m+1) :
  ((BD.data.complex c_ r V r' (k' c' m * c)).obj M).X q' ⟶
    ((BD.data.complex (c' * c_) r V r' c).obj M).X q' :=
(@CLCFPTinv.res r V _ _ r' _ _ _ _ _ ⟨NSH_h_res' hqm⟩).app M

instance NSH_δ_res' (N i : ℕ) (c : ℝ≥0) [hN : fact (k' c' m ≤ 2 ^ N)] :
  fact (k' c' m * c * rescale_constants c_ (2 ^ N) i ≤ c * c_ i) :=
begin
  refine ⟨_⟩,
  calc k' c' m * c * (c_ i * (2 ^ N)⁻¹)
     = (k' c' m * (2 ^ N)⁻¹) * (c * c_ i) : by ring1
  ... ≤ 1 * (c * c_ i) : mul_le_mul' _ le_rfl
  ... = c * c_ i : one_mul _,
  apply mul_inv_le_of_le_mul (pow_ne_zero _ $ @two_ne_zero ℝ≥0 _ _),
  rw one_mul,
  exact hN.1
end

def NSH_δ_res {BD : data} [BD.suitable c_]
  (N : ℕ) [fact (k' c' m ≤ 2 ^ N)] (c : ℝ≥0) {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} :
  ((BD.system c_ r V r').obj M).obj (op c) ⟶
    ((BD.system (rescale_constants c_ (2 ^ N)) r V r').obj M).obj (op (k' c' m * c)) :=
{ f := λ i, (@CLCFPTinv.res r V _ _ r' _ _ _ _ _ (NSH_δ_res' _ _ _)).app M,
  comm :=
  begin
    intros i j, symmetry,
    dsimp [data.system_obj, data.complex],
    refine nat_trans.congr_app (universal_map.res_comp_eval_CLCFPTinv r V r' _ _ _ _ _) M,
  end }

end

def NSH_aux (N : ℕ) (M) :
  NSH_aux_type BD r r' V c_ c' m Λ (N₂ c_ c' r r' m) M :=
{ h := λ q q' c,
    if hqm : q' ≤ m + 1
    then NSH_h_res c hqm ≫ (homotopy_σπ BD c_ c' r V c M _).h q' q
    else 0,
  h_bound_by :=
  begin
    rintro q q' hqm rfl c hc,
    rw [dif_pos (nat.succ_le_succ hqm)],
    refine normed_group_hom.bound_by.comp' 1 _ _ (mul_one _).symm _ _,
    swap, { exact (CLCFPTinv₂.res_norm_noninc r V r' _ _ _ _ _ _).bound_by_one },
    dsimp only [homotopy_σπ, breen_deligne.homotopy, homotopy₂],
    apply universal_map.eval_CLCFPTinv₂_bound_by,
    exact (bound_by_H BD c_ c' r r' _ hqm),
  end,
  δ := λ c, ((BD_system_map (BD.data.proj _) c_ c_ r V).app M).app (op c) ≫ NSH_δ_res _ c,
  hδ := sorry,
  δ_bound_by := sorry }
.

def NSC_htpy :
  normed_spectral_homotopy
    ((thm95.double_complex BD.data c_ r r' V Λ M (N c_ c' r r' m)).row_map 0 1)
      m (k' c' m) (ε m) (c₀ Λ) (H BD c_ c' r r' m) :=
(NSH_aux BD r r' V c_ c' m Λ (N₂ c_ c' r r' m) (op $ (Hom ↥Λ ↥M))).of_iso _ _ _
  (iso.refl _) sorry (λ _ _ _, rfl) sorry sorry

def NSC (IH : ∀ m' < m, thm95.IH BD r r' V c_ c' M m') :
  normed_spectral_conditions (thm95.double_complex BD.data c_ r r' V Λ M (N c_ c' r r' m)) m
    (k₁ m) (K₁ m) (k' c' m) (ε m) (c₀ Λ) (H BD c_ c' r r' m) :=
{ row_exact := NSC_row_exact _ _ _ _ _ _ _ _ _ IH,
  col_exact := sorry,
  htpy := NSC_htpy BD r r' V c_ c' M m Λ,
  admissible := thm95.double_complex_admissible _ }

include BD c_ c' r r' M V m

/-- Theorem 9.5 in [Analytic] -/
theorem thm95 : ∀ (Λ : PolyhedralLattice.{0}) (S : Type) [fintype S]
  (V : NormedGroup) [normed_with_aut r V],
  ​((BD.data.system c_ r V r').obj (op $ Hom Λ (Mbar r' S))).is_weak_bounded_exact
    (k c' m) (K BD c_ c' r r' m) m (c₀ Λ) :=
begin
  apply nat.strong_induction_on m; clear m,
  introsI m IH Λ S _S_fin V _V_r,
  let cond := NSC BD r r' V c_ c' (of r' $ Mbar r' S) m Λ _,
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
