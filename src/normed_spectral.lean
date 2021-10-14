import system_of_complexes.double
import system_of_complexes.truncate
import normed_snake
import category_theory.concrete_category

import thm95.constants.spectral_constants

noncomputable theory
open_locale nnreal
open category_theory

universe variables u

namespace system_of_double_complexes

@[simps]
def truncate : system_of_double_complexes.{u} ⥤ system_of_double_complexes.{u} :=
(whiskering_right _ _ _).obj $
  @functor.map_homological_complex _ _ _ _ _ _ _ _ SemiNormedGroup.truncate.additive.{u} _
-- TODO: why do I need to give the instance manually? ↑ ↑ ↑

namespace truncate

variables (M : system_of_double_complexes.{u})

-- defeq abuse for the win!!!
lemma row (p : ℕ) :
  (truncate.obj M).row p = system_of_complexes.truncate.obj (M.row p) := rfl

lemma col_pos (q : ℕ) :
  (truncate.obj M).col (q+1) = M.col (q+1+1) :=
rfl

@[simp]
lemma d'_zero_one (c : ℝ≥0) (p : ℕ) (x : M.X c p 1) :
  (truncate.obj M).d' 0 1 (SemiNormedGroup.explicit_cokernel_π _ x) = M.d' 1 2 x := rfl

@[simp]
lemma d_π (c : ℝ≥0) (p p' : ℕ) (x : M.X c p 1) :
  @d (truncate.obj M) _ p p' 0 (SemiNormedGroup.explicit_cokernel_π _ x) =
  SemiNormedGroup.explicit_cokernel_π _ (M.d p p' x) := rfl

@[simp]
lemma res_π (c₁ c₂ : ℝ≥0) (p : ℕ) (h : fact (c₁ ≤ c₂)) (x : M.X c₂ p 1) :
  @res (truncate.obj M) _ _ p 0 h (SemiNormedGroup.explicit_cokernel_π _ x) =
  SemiNormedGroup.explicit_cokernel_π _ (M.res x) := rfl

def quotient_map : M.col 1 ⟶ (truncate.obj M).col 0 :=
{ app := λ c,
  { f := λ p, SemiNormedGroup.explicit_cokernel_π _,
    comm' := λ p p' _, by { ext, refl } },
  naturality' := by { intros, ext, refl } }

lemma admissible (hM : M.admissible) : (truncate.obj M).admissible :=
{ d_norm_noninc' := λ c p' p q h,
  begin
    cases q,
    { apply SemiNormedGroup.explicit_cokernel_desc_norm_noninc,
      exact (SemiNormedGroup.norm_noninc_explicit_cokernel_π _).comp (hM.d_norm_noninc _ _ _ _) },
    { exact hM.d_norm_noninc c p' p _ }
  end,
  d'_norm_noninc' := λ c p,
    ((M.row p).truncate_admissible (hM.row p)).d_norm_noninc' c,
  res_norm_noninc := λ c₁ c₂ p,
    ((M.row p).truncate_admissible (hM.row p)).res_norm_noninc c₁ c₂ }

end truncate

open opposite

structure normed_spectral_homotopy {row₀ row₁ : system_of_complexes.{u}} (d : row₀ ⟶ row₁)
  (m : ℕ) (k' ε : ℝ≥0) [fact (1 ≤ k')] (c₀ H : ℝ≥0) [fact (0 < H)] :=
(h : Π (q : ℕ) {q' : ℕ} {c}, row₀ (k' * c) q' ⟶ row₁ c q)
(norm_h_le : ∀ (q q' : ℕ) (hq : q ≤ m) (hq' : q+1 = q') (c) [fact (c₀ ≤ c)],
  ∥(h q : row₀ (k' * c) q' ⟶ row₁ c q)∥ ≤ H)
(δ : Π (c : ℝ≥0), row₀.obj (op $ c) ⟶ row₁.obj (op $ k' * c))
(hδ : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (q : ℕ) (hq : q ≤ m),
  (system_of_complexes.res : row₀ (k' * (k' * c)) q ⟶ _) ≫ (δ c).f q =
    d.apply ≫ system_of_complexes.res + row₀.d q (q+1) ≫ h q + h (q-1) ≫ row₁.d (q-1) q)
(norm_δ_le : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (q : ℕ) (hq : q ≤ m), ∥(δ c).f q∥ ≤ ε)
.

lemma normed_spectral_homotopy.hδ_apply {row₀ row₁ : system_of_complexes.{u}} {d : row₀ ⟶ row₁}
  {m : ℕ} {k' ε : ℝ≥0} [fact (1 ≤ k')] {c₀ H : ℝ≥0} [fact (0 < H)]
  (NSH : normed_spectral_homotopy d m k' ε c₀ H)
  (c : ℝ≥0) [fact (c₀ ≤ c)] (q : ℕ) (hq : q ≤ m) (x : row₀ (k' * (k' * c)) q) :
  (NSH.δ c).f q (system_of_complexes.res x) =
    system_of_complexes.res (d x) + NSH.h q (row₀.d q (q+1) x) + row₁.d (q-1) q (NSH.h (q-1) x) :=
begin
  show ((system_of_complexes.res : row₀ (k' * (k' * c)) q ⟶ _) ≫ (NSH.δ c).f q) x = _,
  rw NSH.hδ c q hq,
  dsimp, refl
end

def normed_spectral_homotopy.of_iso {row₀ row₁ : system_of_complexes.{u}} {d : row₀ ⟶ row₁}
  {m : ℕ} {k' ε : ℝ≥0} [fact (1 ≤ k')] {c₀ H : ℝ≥0} [fact (0 < H)]
  (NSH : normed_spectral_homotopy d m k' ε c₀ H)
  (row'₀ row'₁ : system_of_complexes.{u}) (d' : row'₀ ⟶ row'₁)
  (φ₀ : row₀ ≅ row'₀) (φ₁ : row₁ ≅ row'₁)
  (hφ₀ : ∀ c i (x : row'₀ c i), ∥φ₀.inv x∥ = ∥x∥)
  (hφ₁ : ∀ c i (x : row₁ c i), ∥φ₁.hom x∥ = ∥x∥)
  (hcomm : d' = φ₀.inv ≫ d ≫ φ₁.hom) :
  normed_spectral_homotopy d' m k' ε c₀ H :=
{ h := λ q q' c, φ₀.inv.apply ≫ NSH.h q ≫ φ₁.hom.apply,
  δ := λ c, φ₀.inv.app (op $ c) ≫ NSH.δ c ≫ φ₁.hom.app (op $ k' * c),
  norm_h_le :=
  begin
    introsI q q' hqm hq' c hc,
    refine normed_group_hom.op_norm_le_bound _ (nnreal.coe_nonneg H) (λ x, _),
    calc  ∥φ₁.hom (NSH.h q (φ₀.inv x))∥
        = ∥NSH.h q (φ₀.inv x)∥ : hφ₁ _ _ _
    ... ≤ ↑H * ∥φ₀.inv x∥ :
      normed_group_hom.le_of_op_norm_le _ (NSH.norm_h_le _ _ hqm hq' _) (φ₀.inv x)
    ... = ↑H * ∥x∥ : congr_arg _ (hφ₀ _ _ _),
  end,
  hδ :=
  begin
    introsI c hc q hq,
    ext1 x,
    have := congr_arg (λ x, φ₁.hom x) (NSH.hδ_apply c q hq (φ₀.inv x)),
    simp only [coe_comp, hcomm, system_of_complexes.res_apply, system_of_complexes.d_apply] at this ⊢,
    refine this.trans _, clear this,
    calc φ₁.hom (d (φ₀.inv (system_of_complexes.res x)) +
          (NSH.h q) (φ₀.inv (row'₀.d q (q+1) x)) +
          (row₁.d (q - 1) q) (NSH.h (q - 1) (φ₀.inv x)))
        = φ₁.hom (d (φ₀.inv (system_of_complexes.res x)) +
          (NSH.h q) (φ₀.inv (row'₀.d q (q+1) x))) +
          φ₁.hom ((row₁.d (q - 1) q) (NSH.h (q - 1) (φ₀.inv x))) : _
    ... = _ : _,
    { apply normed_group_hom.map_add },
    congr' 1,
    { refine (normed_group_hom.map_add _ _ _).trans _,
      simp only [← comp_apply, ← system_of_complexes.res_comp_apply], refl },
    { erw [system_of_complexes.d_apply], refl }
  end,
  norm_δ_le := λ c hc q hq,
  begin
    resetI,
    refine normed_group_hom.op_norm_le_bound _ (nnreal.coe_nonneg ε) _,
    rintro (x : row'₀ c q),
    calc  ∥φ₁.hom ((NSH.δ c).f q (φ₀.inv x))∥
        = ∥(NSH.δ c).f q (φ₀.inv x)∥ : hφ₁ _ _ _
    ... ≤ ↑ε * ∥φ₀.inv x∥ : normed_group_hom.le_of_op_norm_le _  (NSH.norm_δ_le _ _ hq) (φ₀.inv x)
    ... = ↑ε * ∥x∥ : congr_arg _ (hφ₀ _ _ _),
  end }

/-- The assumptions on `M` in Proposition 9.6 bundled into a structure. -/
structure normed_spectral_conditions (M : system_of_double_complexes.{u})
  (m : ℕ) (k K k' ε : ℝ≥0) [fact (1 ≤ k)] [fact (1 ≤ k')] (c₀ H : ℝ≥0) [fact (0 < H)] :=
(row_exact : 0 < m → ∀ i ≤ m + 1, (M.row i).is_weak_bounded_exact k K (m-1) c₀)
(col_exact : ∀ j ≤ m, (M.col j).is_weak_bounded_exact k K m c₀)
(htpy      : normed_spectral_homotopy (M.row_map 0 1) m k' ε c₀ H)
-- ergonomics: we bundle this assumption, instead of passing it around separately
(admissible : M.admissible)

.

namespace normed_spectral_conditions

variables {M : system_of_double_complexes.{u}}
variables {m : ℕ} {k K k' ε k₀ : ℝ≥0}
variables [fact (1 ≤ k)] [fact (1 ≤ k₀)] [fact (k₀ ≤ k')] [fact (1 ≤ k')]
variables {c₀ H : ℝ≥0} [fact (0 < H)]

lemma truncate_admissible (condM : M.normed_spectral_conditions m k K k' ε c₀ H) :
  (truncate.obj M).admissible :=
truncate.admissible _ condM.admissible

variables (condM : M.normed_spectral_conditions (m+1) k K k' ε c₀ H)

include condM

lemma col_zero_exact :
  ((truncate.obj M).col 0).is_weak_bounded_exact (k*k*k) (K*(K*K+1)) m c₀ :=
begin
  apply weak_normed_snake (M.col 0) (M.col 1) ((truncate.obj M).col 0)
    (M.col_map 0 1) (truncate.quotient_map M)
    (condM.col_exact 0 dec_trivial) (condM.col_exact 1 dec_trivial)
    (condM.admissible.col 1),
  { intros c p, exact condM.admissible.d'_norm_noninc c p 0 1 },
  { intros c hc i hi x,
    apply le_of_forall_pos_le_add,
    intros ε' hε',
    -- should we factor out a dedicated `weak_bounded_in_degrees_le_zero` lemma?
    simpa only [exists_prop, row_res, d'_self_apply, exists_eq_left, sub_zero,
      exists_and_distrib_left, zero_add, row_d, exists_eq_left', exists_const]
      using condM.row_exact (nat.zero_lt_succ _) i hi c hc 0 (nat.zero_le _) x ε' hε' },
  { intros c i, apply quotient_add_group.ker_mk },
  { intros c p, exact SemiNormedGroup.is_quotient_explicit_cokernel_π _ }
end

-- morally `q'` is `q + 1`
def h_truncate : Π (q : ℕ) {q' : ℕ} {c : ℝ≥0},
  (truncate.obj M).X (k' * c) 0 q' ⟶ (truncate.obj M).X c 1 q
| 0     1      c := condM.htpy.h 1 ≫ SemiNormedGroup.explicit_cokernel_π _
| (q+1) (q'+1) c := condM.htpy.h (q+2)
| _     _      _ := 0

@[simp]
lemma h_truncate_zero {c : ℝ≥0} (x : (truncate.obj M).X (k' * c) 0 1) :
  condM.h_truncate 0 x = SemiNormedGroup.explicit_cokernel_π _ (condM.htpy.h 1 x) := rfl

lemma norm_h_truncate_le : ∀ (q q' : ℕ), q ≤ m → q+1 = q' → ∀ (c : ℝ≥0), fact (c₀ ≤ c) →
  ∥(condM.h_truncate q : (truncate.obj M).X (k' * c) 0 q' ⟶ _)∥ ≤ H
| (q+1) (q'+1) hq rfl := condM.htpy.norm_h_le _ _ (nat.succ_le_succ hq)
                                    (by simp only [nat.add_def, add_zero])
| 0     1      hq rfl :=
begin
  introsI c hc,
  refine normed_group_hom.op_norm_le_bound _ (nnreal.coe_nonneg H) (λ x, _),
  calc _ = ∥SemiNormedGroup.explicit_cokernel_π _ (condM.htpy.h 1 x)∥ : rfl
  ...  ≤ ∥condM.htpy.h 1 x∥ : (SemiNormedGroup.is_quotient_explicit_cokernel_π _).norm_le _
  ... ≤ H * ∥x∥ : normed_group_hom.le_of_op_norm_le _ (condM.htpy.norm_h_le 1 2 dec_trivial rfl c) x
end

def δ_truncate (c : ℝ≥0) :
  ((truncate.obj M).row 0).obj (op $ c) ⟶ ((truncate.obj M).row 1).obj (op $ k' * c) :=
SemiNormedGroup.truncate.map (condM.htpy.δ c)

lemma hδ_truncate (c : ℝ≥0) [fact (c₀ ≤ c)] : ∀ (q : ℕ) (hq : q ≤ m),
  (truncate.obj M).res ≫ (condM.δ_truncate c).f q = (d _ 0 1) ≫ (truncate.obj M).res +
    (d' _ q (q+1)) ≫ condM.h_truncate q + (condM.h_truncate (q-1)) ≫ d' _ (q-1) q
| 1     h := condM.htpy.hδ _ _ (nat.succ_le_succ h)
| (q+2) h := condM.htpy.hδ _ _ (nat.succ_le_succ h)
| 0     h :=
begin
  ext x, dsimp,
  let π := λ c p, SemiNormedGroup.explicit_cokernel_π (@d' M c p 0 1),
  obtain ⟨y, hy⟩ : ∃ x', π _ _ x' = (SemiNormedGroup.explicit_cokernel_π _ x) :=
    SemiNormedGroup.explicit_cokernel_π_surjective (SemiNormedGroup.explicit_cokernel_π _ x),
  transitivity π _ _ ((condM.htpy.δ c).f 1 (M.res x)), { refl },
  erw condM.htpy.hδ_apply _ _ (nat.succ_le_succ h) x,
  simp only [nat.zero_sub, d'_self_apply, add_zero, row_d,
    truncate.d_π, truncate.res_π, truncate.d'_zero_one, h_truncate_zero,
    normed_group_hom.map_add, SemiNormedGroup.explicit_cokernel_π_apply_dom_eq_zero],
  refl
end

lemma norm_δ_truncate_le (c : ℝ≥0) [fact (c₀ ≤ c)] :
  ∀ (q : ℕ) (hq : q ≤ m), ∥(condM.δ_truncate c).f q∥ ≤ ε
| (q+1) h := condM.htpy.norm_δ_le c (q+2) (nat.succ_le_succ h)
| 0     h :=
begin
  refine SemiNormedGroup.explicit_cokernel_desc_norm_le_of_norm_le _ _
    (normed_group_hom.op_norm_le_bound _ (nnreal.coe_nonneg ε) (λ x, _)),
  refine (SemiNormedGroup.norm_noninc_explicit_cokernel_π _ _).trans _,
  exact normed_group_hom.le_of_op_norm_le _ (condM.htpy.norm_δ_le c _ (nat.succ_le_succ h)) _
end

def truncate :
  (truncate.obj M).normed_spectral_conditions m (k*k*k) (K*(K*K+1)) k' ε c₀ H :=
{ row_exact :=
  begin
    intros hm i hi,
    cases m, { exact (nat.not_lt_zero _ hm).elim },
    suffices : ((truncate.obj M).row i).is_weak_bounded_exact k K m c₀,
    { apply this.of_le (condM.truncate_admissible.row i) _ _ le_rfl ⟨le_rfl⟩;
      apply_instance },
    rw truncate.row,
    apply (M.row i).truncate_is_weak_bounded_exact,
    { refine condM.row_exact (nat.zero_lt_succ _) i (hi.trans (nat.le_succ _)), }
  end,
  col_exact :=
  begin
    rintro (j|j) hj,
    { exact condM.col_zero_exact },
    { rw truncate.col_pos,
      refine (condM.col_exact (j+2) (nat.succ_le_succ hj)).of_le
        (condM.admissible.col (j+2)) _ _ m.le_succ ⟨le_rfl⟩;
      apply_instance }
  end,
  htpy :=
  { h := condM.h_truncate,
    norm_h_le := condM.norm_h_truncate_le,
    δ := condM.δ_truncate,
    hδ := condM.hδ_truncate,
    norm_δ_le := condM.norm_δ_truncate_le },
  admissible := condM.truncate_admissible }

omit condM

variables {m_ : ℕ} {k_ K_ : ℝ≥0} [fact (1 ≤ k_)]
variables {ε_ : ℝ≥0} {k₀_ : ℝ≥0} [fact (1 ≤ k₀_)]
variables [fact (k₀_ ≤ k')] {c₀_ H_ : ℝ≥0} [fact (0 < H_)]

def of_le (cond : M.normed_spectral_conditions m k K k' ε c₀ H)
  (hm : m_ ≤ m) (hk : fact (k ≤ k_)) (hK : fact (K ≤ K_)) (hε : ε ≤ ε_)
  (hc₀ : fact (c₀ ≤ c₀_)) (hH : H ≤ H_) :
  M.normed_spectral_conditions m_ k_ K_ k' ε_ c₀_ H_ :=
{ col_exact := λ j hj, (cond.col_exact j (hj.trans hm)).of_le (cond.admissible.col j) hk hK hm hc₀,
  row_exact := λ hm_ i hi,
    (cond.row_exact (hm_.trans_le hm) i (hi.trans $ nat.succ_le_succ hm)).of_le
      (cond.admissible.row i) hk hK (nat.pred_le_pred hm) hc₀,
  htpy :=
  { h := cond.htpy.h,
    norm_h_le := λ q q' hq hq' c hc, have fact (c₀ ≤ c) := ⟨hc₀.out.trans hc.out⟩, by exactI
    begin
    refine normed_group_hom.op_norm_le_bound _ (nnreal.coe_nonneg H_) (λ x, _),
    calc ∥cond.htpy.h q x∥ ≤ H * ∥x∥  :
      normed_group_hom.le_of_op_norm_le _ (cond.htpy.norm_h_le q q' (hq.trans hm) hq' c) x
                       ... ≤ H_ * ∥x∥ : mul_le_mul_of_nonneg_right hH (norm_nonneg x),
    end,
    δ := cond.htpy.δ,
    hδ := λ c hc q hq, have fact (c₀ ≤ c) := ⟨hc₀.out.trans hc.out⟩,
      by exactI cond.htpy.hδ c q (hq.trans hm),
    norm_δ_le := λ c hc q hq, have fact (c₀ ≤ c) := ⟨hc₀.out.trans hc.out⟩, by exactI
    begin
      refine normed_group_hom.op_norm_le_bound _ (nnreal.coe_nonneg ε_) (λ x, _),
      refine normed_group_hom.le_of_op_norm_le _ _ x,
      exact le_trans (cond.htpy.norm_δ_le c q (hq.trans hm)) hε,
    end },
  admissible := cond.admissible }

end normed_spectral_conditions

namespace normed_spectral

/-- Base case of the induction for Proposition 9.6. -/
theorem base (c₀ H : ℝ≥0) [fact (0 < H)] (M : system_of_double_complexes.{u})
  (k K k' : ℝ≥0) [hk : fact (1 ≤ k)] [hK : fact (1 ≤ K)] [fact (k₀ 0 k ≤ k')] [fact (1 ≤ k')]
  (cond : M.normed_spectral_conditions 0 k K k' (ε 0 K) c₀ H) :
  (M.row 0).is_weak_bounded_exact (k' * k') (2 * K₀ 0 K * H) 0 c₀ :=
begin
  dsimp [k₀, K₀],
  introsI c hc i hi,
  interval_cases i, clear hi,
  intros x ε' hε',
  let φ : ℝ := ε' / 2,
  have hφ : 0 < φ := div_pos hε' zero_lt_two,
  have hδφ : ε' = φ + φ, { dsimp [φ], rw [← add_div, half_add_self] },
  haveI : fact (k' * (k' * c) ≤ k' * k' * c) := by { rw mul_assoc, exact ⟨le_rfl⟩ },
  have Hx1 := (cond.col_exact 0 le_rfl).of_le
    (cond.admissible.col 0) ‹_› ⟨le_rfl⟩ le_rfl ⟨le_rfl⟩ c hc 0 le_rfl,
  have Hx2 := normed_group_hom.le_of_op_norm_le _ (cond.htpy.norm_δ_le c 0 le_rfl) (M.res x),
  have aux := cond.htpy.hδ_apply c 0 le_rfl (M.res x),
  erw [res_res] at aux,
  rw aux at Hx2,
  simp only [row_d, col_d, d_self_apply, d'_self_apply, sub_zero, add_zero, smul_zero,
    d_res, d'_res, res_res, one_div, row_res, units.coe_one, one_smul, row_map_apply] at Hx1 Hx2 ⊢,
  refine ⟨0, 1, rfl, rfl, 0, _⟩,
  obtain ⟨i, j, hi, hj, y1, hx1⟩ := Hx1 (M.res x) φ hφ,
  simp [← eq_neg_iff_add_eq_zero] at hi hj, subst i, subst j,
  simp only [d_self_apply, d'_self_apply, sub_zero,
    nnreal.coe_mul, nnreal.coe_bit0, nnreal.coe_one, d_res] at hx1 ⊢,
  erw [res_res] at hx1,
  clear y1 Hx1,
  replace Hx1 := mul_le_mul_of_nonneg_left hx1 (ε 0 K).coe_nonneg,
  replace Hx2 := (norm_le_add_norm_add _ _).trans (add_le_add (Hx2.trans Hx1) le_rfl),
  dsimp [ε] at Hx2,
  have K0 : (K:ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK.out),
  simp only [mul_add, add_assoc, mul_inv₀, mul_assoc, inv_mul_cancel_left₀ K0] at Hx2,
  simp only [← div_eq_inv_mul, sub_half, ← sub_le_iff_le_add'] at Hx2,
  simp only [sub_le_iff_le_add', div_le_iff' (zero_lt_two : (0:ℝ) < 2)] at Hx2,
  replace Hx2 := mul_le_mul_of_nonneg_left Hx2 K.coe_nonneg,
  simp only [mul_add, div_eq_inv_mul, add_comm φ,
    mul_inv_cancel_left₀ (two_ne_zero : (2:ℝ) ≠ 0), mul_inv_cancel_left₀ K0] at Hx2,
  refine hx1.trans _,
  simp only [mul_comm (2:ℝ) K, mul_assoc, hδφ, ← add_assoc, ← mul_add, add_le_add_iff_right],
  refine Hx2.trans _,
  simp only [add_le_add_iff_right],
  refine (mul_le_mul_of_nonneg_left _ K.coe_nonneg),
  refine (mul_le_mul_of_nonneg_left _ zero_le_two),
  refine le_trans (normed_group_hom.le_of_op_norm_le _ (cond.htpy.norm_h_le _ _ le_rfl rfl _) _) _,
  refine mul_le_mul_of_nonneg_left (le_of_eq _) H.coe_nonneg,
  apply norm_res_of_eq,
  rw mul_assoc
end
.

end normed_spectral

open normed_spectral

/-- Proposition 9.6 in [Analytic] -/
theorem normed_spectral {m : ℕ} {c₀ H : ℝ≥0} [fact (0 < H)]
  {M : system_of_double_complexes.{u}} {k K k' : ℝ≥0}
  [fact (1 ≤ k)] [hK : fact (1 ≤ K)] [fact (k₀ m k ≤ k')] [fact (1 ≤ k')]
  (cond : M.normed_spectral_conditions m k K k' (ε m K) c₀ H) :
  (M.row 0).is_weak_bounded_exact (k' * k') (2 * K₀ m K * H) m c₀ :=
begin
  unfreezingI { revert M k K k' },
  induction m with m IH, { exact base c₀ H },
  dsimp [ε, k₀, K₀],
  introsI M k K k' _ _ _ _ cond,
  rw ← system_of_complexes.truncate_is_weak_bounded_exact_iff,
  { exact IH cond.truncate },
  { refine @IH M (k*k*k) (K*(K*K+1)) k' _ _ _ _ (cond.of_le (m.le_succ) _ _ le_rfl ⟨le_rfl⟩ le_rfl),
    all_goals { apply_instance } }
end

end system_of_double_complexes
