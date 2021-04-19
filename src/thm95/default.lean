import polyhedral_lattice.Hom
import Mbar.pseudo_normed_group

import normed_spectral

import pseudo_normed_group.homotopy

import thm95.constants
import thm95.double_complex
import thm95.row_iso

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
    (k c' m) (K BD c' r r' m) m (c₀ m Λ)

omit BD c_ c' r r' M V

lemma NSC_row_exact (IH : ∀ m' < m, thm95.IH BD r r' V c_ c' M m')
  (h0m : 0 < m) (i : ℕ) (hi : i ≤ m + 1) :
  ((thm95.double_complex BD.data c_ r r' V Λ M (N c' r r' m)).row i).is_weak_bounded_exact
    (k₁ m) (K₁ m) (m - 1) (c₀ m Λ) :=
begin
  haveI h0m_ : fact (0 < m) := ⟨h0m⟩,
  have hm' : m - 1 < m := nat.pred_lt h0m.ne',
  rcases i with (i|i|i),
  { rw thm95.double_complex.row_zero,
    refine (IH (m-1) hm' Λ).of_le BD.data.system_admissible _ _ le_rfl ⟨le_rfl⟩,
    all_goals { apply_instance } },
  { rw thm95.double_complex.row_one,
    refine (IH (m-1) hm' _).of_le BD.data.system_admissible _ _ le_rfl _,
    swap 3,
    { apply c₀_pred_le c' r r' Λ m h0m },
    all_goals { apply_instance } },
  { rw thm95.double_complex.row,
    apply system_of_complexes.rescale_is_weak_bounded_exact,
    refine (IH (m-1) hm' _).of_le BD.data.system_admissible _ _ le_rfl _,
    swap 3,
    { apply c₀_pred_le_of_le c' r r' Λ m i hi },
    all_goals { apply_instance } }
end
.

def NSH_aux_type (N : ℕ) (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :=
normed_spectral_homotopy
  ((BD_system_map (BD.data.sum (2^N)) c_ (rescale_constants c_ (2^N)) r V).app M)
  m (k' c' m) (ε m) (c₀ m Λ) (H BD c' r r' m)

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

def NSH_h {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (q q' : ℕ) (c : ℝ≥0) :
  ((BD.data.system c_ r V r').obj M) (k' c' m * c) q' ⟶
    ((((data.mul (2 ^ N₂ c' r r' m)).obj BD.data).system
      (rescale_constants c_ (2 ^ N₂ c' r r' m)) r V r').obj M) c q :=
if hqm : q' ≤ m + 1
  then NSH_h_res c hqm ≫ (homotopy_σπ BD c_ c' r V c M _).h q' q
  else 0

lemma NSH_h_bound_by {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ}
  (q : ℕ) (hqm : q ≤ m) (c : ℝ≥0) [fact (c₀ m Λ ≤ c)] :
  normed_group_hom.bound_by
    (@NSH_h BD r r' _ _ _ _ V _ c_ c' _ _ m M q (q+1) c)
    (H BD c' r r' m) :=
begin
  rw [NSH_h, dif_pos (nat.succ_le_succ hqm)],
  refine normed_group_hom.bound_by.comp' 1 _ _ (mul_one _).symm _ _,
  swap, { exact (CLCFPTinv₂.res_norm_noninc r V r' _ _ _ _ _ _).bound_by_one },
  dsimp only [homotopy_σπ, breen_deligne.homotopy, homotopy₂],
  apply universal_map.eval_CLCFPTinv₂_bound_by,
  exact (bound_by_H BD c' r r' _ hqm),
end

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

variables (c')

@[simps f]
def NSH_δ_res {BD : data} [BD.suitable c_]
  (N : ℕ) [fact (k' c' m ≤ 2 ^ N)] (c : ℝ≥0) {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} :
  ((BD.system c_ r V r').obj M).obj (op c) ⟶
    ((BD.system (rescale_constants c_ (2 ^ N)) r V r').obj M).obj (op (k' c' m * c)) :=
{ f := λ i, (@CLCFPTinv.res r V _ _ r' _ _ _ _ _ (NSH_δ_res' _ _ _)).app M,
  comm :=
  begin
    intros i j, symmetry,
    dsimp [data.system_obj, data.complex],
    exact nat_trans.congr_app (universal_map.res_comp_eval_CLCFPTinv r V r' _ _ _ _ _) M,
  end }
.

variables {c'}

def NSH_δ {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (c : ℝ≥0) :
  ((BD.data.system c_ r V r').obj M).obj (op c) ⟶
    ((((data.mul (2 ^ N₂ c' r r' m)).obj BD.data).system
      (rescale_constants c_ (2 ^ N₂ c' r r' m)) r V r').obj M).obj (op (k' c' m * c)) :=
NSH_δ_res c' (N₂ c' r r' m) _ ≫ (BD_map (BD.data.proj (2 ^ N₂ c' r r' m)) _ _ r V _).app M

lemma NSH_δ_bound_by {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (c : ℝ≥0) (q : ℕ) :
  normed_group_hom.bound_by ((@NSH_δ BD r r' _ _ _ _ V _ c_ c' _ _ m M c).f q) (ε m) :=
begin
  refine (normed_group_hom.bound_by.comp'
    (r ^ (b c' r r' m)) (N c' r r' m) _ (mul_comm _ _) _ _).le _,
  { apply universal_map.eval_CLCFPTinv₂_bound_by,
    apply universal_map.proj_bound_by },
  { refine @CLCFPTinv.res_bound_by_pow r V _ _ r' _ _ _ _ _ _ _ ⟨_⟩ _,
    dsimp only [unop_op, rescale_constants],
    simp only [← mul_assoc, mul_right_comm _ c],
    simp only [mul_right_comm _ (c_ q)],
    apply mul_le_mul' _ le_rfl,
    apply mul_le_mul' _ le_rfl,
    apply N₂_spec },
  { apply r_pow_b_le_ε }
end

variables (V c' m)

-- move this, and rename (all of these?)
instance aux0 (q : ℕ) [hq : fact (q ≤ m)] :
  fact (c' q ≤ k' c' m) :=
⟨c'_le_k' _ _ $ hq.1.trans $ nat.le_succ _⟩

instance aux1 (c : ℝ≥0) (q : ℕ) [fact (q ≤ m)] :
  ((BD.data.proj (2 ^ N₂ c' r r' m)).f q).suitable
    (k' c' m * c * rescale_constants c_ (2 ^ N₂ c' r r' m) q) (c * c_ q) :=
begin
  refine universal_map.suitable.le _ (c * c_ q) (c * c_ q) (c * c_ q) _ _ le_rfl,
  { apply_instance },
  have : k' c' m / 2 ^ N₂ c' r r' m ≤ r' ^ b c' r r' m := N₂_spec c' r r' m,
  calc k' c' m * c * (c_ q * (2 ^ N₂ c' r r' m)⁻¹)
     = (k' c' m * (2 ^ N₂ c' r r' m)⁻¹) * (c * c_ q) : by ring1
  ... ≤ 1 * (c * c_ q) : mul_le_mul' (this.trans $ fact.out _) le_rfl
  ... = c * c_ q : one_mul _
end

instance aux2 (c : ℝ≥0) (q : ℕ) [fact (q ≤ m)] :
  ((BD.data.proj (2 ^ N₂ c' r r' m)).f q).suitable
    (k' c' m * c * rescale_constants c_ (2 ^ N₂ c' r r' m) q) (k' c' m * (k' c' m * c) * c_ q) :=
(aux1 c' m c q).le _ _ _ _ le_rfl (fact.out _)

/- use `q ≤ m` and the def'n of `k'` -/
instance aux3 (c : ℝ≥0) (q : ℕ) [fact (q ≤ m)] :
  fact ((k' c' m * c * (c' * c_) q) ≤ (k' c' m * (k' c' m * c) * c_ q)) :=
by { simp only [mul_assoc, mul_left_comm _ c, pi.mul_apply], apply_instance }

instance aux4 (c : ℝ≥0) (q : ℕ) [hq : fact (q ≤ m)] :
  fact (k' c' m * c * (c' (q + 1) * c_ (q + 1)) ≤ k' c' m * (k' c' m * c) * c_ (q + 1)) :=
begin
  simp only [mul_assoc, mul_left_comm _ c],
  haveI : fact (c' (q+1) ≤ k' c' m) := ⟨c'_le_k' _ _ $ nat.succ_le_succ hq.1⟩,
  apply_instance
end

open differential_object differential_object.complex_like category_theory.preadditive

lemma NSH_hδ (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ)
  (c : ℝ≥0) (hc : fact (c₀ m Λ ≤ c)) (q : ℕ) (hqm : q ≤ m) :
  system_of_complexes.res ≫ (NSH_δ c).f q =
    ((BD_system_map (BD.data.sum (2 ^ N₂ c' r r' m))
      c_ (rescale_constants c_ (2 ^ N₂ c' r r' m)) r V).app M).apply ≫ system_of_complexes.res +
    ((BD.data.system c_ r V r').obj M).d q (q + 1) ≫ NSH_h q (q + 1) (k' c' m * c) +
    NSH_h (q - 1) q (k' c' m * c) ≫
      ((((data.mul (2 ^ N₂ c' r r' m)).obj BD.data).system
        (rescale_constants c_ (2 ^ N₂ c' r r' m)) r V r').obj M).d (q - 1) q :=
begin
  haveI hqm_ : fact (q ≤ m) := ⟨hqm⟩,
  rw [NSH_δ, NSH_h, NSH_h, dif_pos (nat.succ_le_succ hqm), dif_pos (hqm.trans (nat.le_succ _))],
  erw [comp_f, BD_map_app_f, NSH_δ_res_f, ← universal_map.eval_CLCFPTinv_def],
  dsimp only [unop_op, NSH_h_res, data.system_res_def],
  simp only [← nat_trans.comp_app],
  rw [universal_map.res_comp_eval_CLCFPTinv_absorb,
      universal_map.res_comp_eval_CLCFPTinv_absorb,
      ← universal_map.res_comp_eval_CLCFPTinv_absorb _ _ _ _ (k' c' m * c * (c' * c_) q)],
  have hcomm := (homotopy_σπ BD c_ c' r V (k' c' m * c) M (N₂ c' r r' m)).comm (q-1) q (q+1),
  rw [differential_object.complex_like.htpy_idx_rel₁_tt_nat,
      differential_object.complex_like.htpy_idx_rel₂_tt_nat] at hcomm,
  specialize hcomm _ rfl,
  { unfreezingI { cases q },
    { simp only [nat.one_ne_zero, false_or, and_self] },
    { simp only [nat.succ_sub_succ_eq_sub, nat.succ_ne_zero, or_false, nat.sub_zero, and_false] } },
  rw [eq_comm, sub_eq_iff_eq_add', BD_map_app_f,
      ← universal_map.eval_CLCFPTinv_def] at hcomm,
  rw [nat_trans.comp_app, hcomm, add_assoc],
  clear hcomm,
  simp only [comp_add],
  congr' 1,
  { dsimp only [category_theory.has_hom.hom.apply, BD_system_map_app_app, BD_map_app_f],
    exact nat_trans.congr_app (universal_map.res_comp_eval_CLCFPTinv₂ _ _ _ _ _ _ _ _ _ _ _ _) M },
  rw add_comm,
  congr' 1,
  { simp only [← category.assoc],
    congr' 1,
    dsimp only [data.system_obj_d, data.complex_obj_d],
    exact nat_trans.congr_app (universal_map.res_comp_eval_CLCFPTinv _ _ _ _ _ _ _ _) M },
end
.

-- #check NSH_hδ V c' m Λ (op M)

end

def NSH_aux' (M) (help_me) : NSH_aux_type BD r r' V c_ c' m Λ (N₂ c' r r' m) M :=
{ h := λ q q' c, NSH_h q q' c,
  h_bound_by := by { rintro q q' hqm rfl, apply NSH_h_bound_by Λ q hqm },
  δ := NSH_δ,
  hδ := help_me,
  δ_bound_by := λ c hc q hqm, by apply NSH_δ_bound_by }
.

open differential_object differential_object.complex_like category_theory.preadditive

def NSH_aux (M) : NSH_aux_type BD r r' V c_ c' m Λ (N₂ c' r r' m) M :=
NSH_aux' BD r r' V c_ c' m Λ M $ λ c hc q hqm,
by convert NSH_hδ V c' m Λ M c hc q hqm
.

def NSC_htpy :
  normed_spectral_homotopy
    ((thm95.double_complex BD.data c_ r r' V Λ M (N c' r r' m)).row_map 0 1)
      m (k' c' m) (ε m) (c₀ m Λ) (H BD c' r r' m) :=
(NSH_aux BD r r' V c_ c' m Λ (op $ (Hom ↥Λ ↥M))).of_iso _ _ _
  (iso.refl _) sorry -- (thm95.mul_rescale_iso_row_one BD.data c_ r V _ Λ M) -- timeout :sad:
  (λ _ _ _, rfl) sorry sorry

def NSC (IH : ∀ m' < m, thm95.IH BD r r' V c_ c' M m') :
  normed_spectral_conditions (thm95.double_complex BD.data c_ r r' V Λ M (N c' r r' m)) m
    (k₁ m) (K₁ m) (k' c' m) (ε m) (c₀ m Λ) (H BD c' r r' m) :=
{ row_exact := NSC_row_exact _ _ _ _ _ _ _ _ _ IH,
  col_exact := sorry,
  htpy := NSC_htpy BD r r' V c_ c' M m Λ,
  admissible := thm95.double_complex_admissible _ }

include BD c_ c' r r' M V m

/-- Theorem 9.5 in [Analytic] -/
theorem thm95 : ∀ (Λ : PolyhedralLattice.{0}) (S : Type) [fintype S]
  (V : NormedGroup) [normed_with_aut r V],
  ​((BD.data.system c_ r V r').obj (op $ Hom Λ (Mbar r' S))).is_weak_bounded_exact
    (k c' m) (K BD c' r r' m) m (c₀ m Λ) :=
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
