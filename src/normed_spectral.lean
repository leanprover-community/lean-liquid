import system_of_complexes.double
import system_of_complexes.truncate
import normed_snake

noncomputable theory
open_locale nnreal
open category_theory

universe variables u

namespace system_of_double_complexes

@[simps]
def truncate : system_of_double_complexes.{u} ⥤ system_of_double_complexes.{u} :=
(whiskering_right _ _ _).obj $
  @functor.map_complex_like _ _ _ _ _ _ _ _ _ _ NormedGroup.truncate.additive.{u u}
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
  (truncate.obj M).d' 0 1 (NormedGroup.coker.π x) = M.d' 1 2 x := rfl

@[simp]
lemma d_π (c : ℝ≥0) (p p' : ℕ) (x : M.X c p 1) :
  @d (truncate.obj M) _ p p' 0 (NormedGroup.coker.π x) = NormedGroup.coker.π (M.d p p' x) := rfl

@[simp]
lemma res_π (c₁ c₂ : ℝ≥0) (p : ℕ) (h : fact (c₁ ≤ c₂)) (x : M.X c₂ p 1) :
  @res (truncate.obj M) _ _ p 0 h (NormedGroup.coker.π x) = NormedGroup.coker.π (M.res x) := rfl

def quotient_map : M.col 1 ⟶ (truncate.obj M).col 0 :=
{ app := λ c,
  { f := λ p, NormedGroup.coker.π,
    comm := λ p p', by { ext, refl } },
  naturality' := by { intros, ext, refl } }

lemma admissible (hM : M.admissible) : (truncate.obj M).admissible :=
{ d_norm_noninc' := λ c p' p q h,
  begin
    cases q,
    { apply NormedGroup.coker.lift_norm_noninc,
      exact NormedGroup.coker.π_norm_noninc.comp (hM.d_norm_noninc _ _ _ _) },
    { exact hM.d_norm_noninc c p' p _ }
  end,
  d'_norm_noninc' := λ c p,
    ((M.row p).truncate_admissible (hM.row p)).d_norm_noninc' c,
  res_norm_noninc := λ c₁ c₂ p,
    ((M.row p).truncate_admissible (hM.row p)).res_norm_noninc c₁ c₂ }

end truncate

open opposite

/-- The assumptions on `M` in Proposition 9.6 bundled into a structure. -/
structure normed_spectral_conditions (M : system_of_double_complexes.{u})
  (m : ℕ) (k K k' ε : ℝ≥0) [fact (1 ≤ k)] [fact (1 ≤ k')] (c₀ H : ℝ≥0) [fact (0 < H)] :=
(col_exact : ∀ j ≤ m, (M.col j).is_weak_bounded_exact k K m c₀)
(row_exact : 0 < m → ∀ i ≤ m + 1, (M.row i).is_weak_bounded_exact k K (m-1) c₀)
(h : Π (q : ℕ) {q' : ℕ} {c}, M.X (k' * c) 0 q' ⟶ M.X c 1 q)
(h_bound_by : ∀ (q q' : ℕ) (hq : q ≤ m) (hq' : q+1 = q') (c) [fact (c₀ ≤ c)],
  (h q : M.X (k' * c) 0 q' ⟶ M.X c 1 q).bound_by H)
-- `δ` only needs to be a map of complexes in degrees `≤ m`; we might need to weaken this
(δ : Π (c : ℝ≥0), (M.row 0).obj (op $ c) ⟶ (M.row 1).obj (op $ k' * c))
(hδ : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (q : ℕ) (hq : q ≤ m) (x : M.X (k' * (k' * c)) 0 q),
  (δ c).f q (M.res x) = M.res (M.d 0 1 x) + h q (M.d' q (q+1) x) + M.d' (q-1) q (h (q-1) x))
(δ_bound_by : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (q : ℕ) (hq : q ≤ m), ((δ c).f q).bound_by ε)
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
  { -- we probably need to weaken this assumption in `weak_normed_snake`
    -- currently this is not provable, because `ker` is only the topological closure of `range`
    sorry },
  { intros c p, exact NormedGroup.coker.π_is_quotient }
end

-- morally `q'` is `q + 1`
def h_truncate : Π (q : ℕ) {q' : ℕ} {c : ℝ≥0},
  (truncate.obj M).X (k' * c) 0 q' ⟶ (truncate.obj M).X c 1 q
| 0     1      c := condM.h 1 ≫ NormedGroup.coker.π
| (q+1) (q'+1) c := condM.h (q+2)
| _     _      _ := 0

@[simp]
lemma h_truncate_zero {c : ℝ≥0} (x : (truncate.obj M).X (k' * c) 0 1) :
  condM.h_truncate 0 x = NormedGroup.coker.π (condM.h 1 x) := rfl

lemma h_truncate_bound_by : ∀ (q q' : ℕ), q ≤ m → q+1 = q' → ∀ (c : ℝ≥0), fact (c₀ ≤ c) →
  (condM.h_truncate q : (truncate.obj M).X (k' * c) 0 q' ⟶ _).bound_by H
| (q+1) (q'+1) hq rfl := condM.h_bound_by _ _ (nat.succ_le_succ hq)
                                    (by simp only [nat.add_def, add_zero])
| 0     1      hq rfl :=
begin
  introsI c hc x,
  calc ∥NormedGroup.coker.π (condM.h 1 x)∥
      ≤ ∥condM.h 1 x∥ : normed_group_hom.quotient_norm_le (NormedGroup.coker.π_is_quotient) _
  ... ≤ H * ∥x∥ : condM.h_bound_by 1 2 dec_trivial rfl c x
end

def δ_truncate (c : ℝ≥0) :
  ((truncate.obj M).row 0).obj (op $ c) ⟶ ((truncate.obj M).row 1).obj (op $ k' * c) :=
NormedGroup.truncate.map (condM.δ c)

lemma hδ_truncate (c : ℝ≥0) [fact (c₀ ≤ c)] : ∀ (q : ℕ) (hq : q ≤ m) (x),
  (condM.δ_truncate c).f q (res _ x) = (truncate.obj M).res (d _ 0 1 x) +
    condM.h_truncate q (d' _ q (q+1) x) + d' _ (q-1) q (condM.h_truncate (q-1) x)
| 1     h := condM.hδ _ _ (nat.succ_le_succ h)
| (q+2) h := condM.hδ _ _ (nat.succ_le_succ h)
| 0     h :=
begin
  intro x,
  let π := λ c p, @NormedGroup.coker.π _ _ (@d' M c p 0 1),
  obtain ⟨x, rfl⟩ : ∃ x', π _ _ x' = x := NormedGroup.coker.π_surjective x,
  have := condM.hδ _ _ (nat.succ_le_succ h) x,
  transitivity π _ _ ((condM.δ c).f 1 (M.res x)), { refl },
  simp only [nat.zero_sub, d'_self_apply, add_zero,
    truncate.d_π, truncate.res_π, truncate.d'_zero_one, h_truncate_zero,
    this, normed_group_hom.map_add, NormedGroup.coker.pi_apply_dom_eq_zero]
end

lemma δ_truncate_bound_by (c : ℝ≥0) [fact (c₀ ≤ c)] :
  ∀ (q : ℕ) (hq : q ≤ m), ((condM.δ_truncate c).f q).bound_by ε
| (q+1) h := condM.δ_bound_by c (q+2) (nat.succ_le_succ h)
| 0     h :=
begin
  refine NormedGroup.coker.lift_bound_by _,
  intro x,
  refine (NormedGroup.coker.π_norm_noninc _).trans _,
  exact condM.δ_bound_by c _ (nat.succ_le_succ h) _
end

def truncate :
  (truncate.obj M).normed_spectral_conditions m (k*k*k) (K*(K*K+1)) k' ε c₀ H :=
{ col_exact :=
  begin
    rintro (j|j) hj,
    { exact condM.col_zero_exact },
    { rw truncate.col_pos,
      refine (condM.col_exact (j+2) (nat.succ_le_succ hj)).of_le
        (condM.admissible.col (j+2)) _ _ m.le_succ le_rfl;
      apply_instance }
  end,
  row_exact :=
  begin
    intros hm i hi,
    cases m, { exact (nat.not_lt_zero _ hm).elim },
    suffices : ((truncate.obj M).row i).is_weak_bounded_exact k K m c₀,
    { apply this.of_le (condM.truncate_admissible.row i) _ _ le_rfl le_rfl;
      apply_instance },
    rw truncate.row,
    apply (M.row i).truncate_is_weak_bounded_exact,
    { refine condM.row_exact (nat.zero_lt_succ _) i (hi.trans (nat.le_succ _)), }
  end,
  h := condM.h_truncate,
  h_bound_by := condM.h_truncate_bound_by,
  δ := condM.δ_truncate,
  hδ := condM.hδ_truncate,
  δ_bound_by := condM.δ_truncate_bound_by,
  admissible := condM.truncate_admissible }

omit condM

variables {m_ : ℕ} {k_ K_ : ℝ≥0} [fact (1 ≤ k_)]
variables {ε_ : ℝ≥0} {k₀_ : ℝ≥0} [fact (1 ≤ k₀_)]
variables [fact (k₀_ ≤ k')] [fact (1 ≤ k')] {c₀_ H_ : ℝ≥0} [fact (0 < H_)]

def of_le (cond : M.normed_spectral_conditions m k K k' ε c₀ H)
  (hm : m_ ≤ m) (hk : fact (k ≤ k_)) (hK : fact (K ≤ K_)) (hε : ε ≤ ε_)
  (hc₀ : fact (c₀ ≤ c₀_)) (hH : H ≤ H_) :
  M.normed_spectral_conditions m_ k_ K_ k' ε_ c₀_ H_ :=
{ col_exact := λ j hj, (cond.col_exact j (hj.trans hm)).of_le (cond.admissible.col j) hk hK hm hc₀,
  row_exact := λ hm_ i hi,
    (cond.row_exact (hm_.trans_le hm) i (hi.trans $ nat.succ_le_succ hm)).of_le
      (cond.admissible.row i) hk hK (nat.pred_le_pred hm) hc₀,
  h := cond.h,
  h_bound_by := λ q q' hq hq' c hc x, have fact (c₀ ≤ c) := le_trans hc₀ hc, by exactI
  calc ∥cond.h q x∥ ≤ H * ∥x∥  : cond.h_bound_by q q' (hq.trans hm) hq' c x
                  ... ≤ H_ * ∥x∥ : mul_le_mul_of_nonneg_right hH (norm_nonneg x),
  δ := cond.δ,
  hδ := λ c hc q hq, have fact (c₀ ≤ c) := le_trans hc₀ hc,
    by exactI cond.hδ c q (hq.trans hm),
  δ_bound_by := λ c hc q hq x, have fact (c₀ ≤ c) := le_trans hc₀ hc, by exactI
    (cond.δ_bound_by c q (hq.trans hm) x).trans (mul_le_mul_of_nonneg_right hε (norm_nonneg _)),
  admissible := cond.admissible }

end normed_spectral_conditions

namespace normed_spectral

noncomputable
def ε : Π (m : ℕ) (K : ℝ≥0), ℝ≥0
| 0     K := (2 * K)⁻¹
| (m+1) K := ε m (K * (K * K + 1))

lemma ε_pos : ∀ m K [fact (1 ≤ K)], 0 < ε m K
| 0     K hK := nnreal.inv_pos.mpr (mul_pos zero_lt_two (lt_of_lt_of_le zero_lt_one hK))
| (m+1) K hK := by { dsimp [ε], exactI ε_pos m _ }

noncomputable
def k₀ : Π (m : ℕ) (k : ℝ≥0), ℝ≥0
| 0     k := k
| (m+1) k := k₀ m (k * k * k)

instance one_le_k₀ : ∀ m k [fact (1 ≤ k)], fact (1 ≤ k₀ m k)
| 0     k hk := hk
| (m+1) k hk := by { dsimp [k₀], exactI one_le_k₀ m _ }

noncomputable
def K₀ : Π (m : ℕ) (K : ℝ≥0), ℝ≥0
| 0     K := K
| (m+1) K := K₀ m (K * (K * K + 1))

instance one_le_K₀ : ∀ m K [fact (1 ≤ K)], fact (1 ≤ K₀ m K)
| 0     K hK := hK
| (m+1) K hK := by { dsimp [K₀], exactI one_le_K₀ m _ }

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
  haveI : fact (k' * (k' * c) ≤ k' * k' * c) := by { rw mul_assoc, exact le_rfl },
  have Hx1 := (cond.col_exact 0 le_rfl).of_le
    (cond.admissible.col 0) ‹_› le_rfl le_rfl le_rfl c hc 0 le_rfl,
  have Hx2 := cond.δ_bound_by c 0 le_rfl (M.res x),
  have aux := cond.hδ c 0 le_rfl (M.res x),
  rw [res_res] at aux,
  rw aux at Hx2,
  simp only [row_d, col_d, d_self_apply, d'_self_apply, sub_zero, add_zero, smul_zero,
    d_res, d'_res, res_res, one_div, row_res, units.coe_one, one_smul] at Hx1 Hx2 ⊢,
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
  have K0 : (K:ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK),
  simp only [mul_add, add_assoc, mul_inv', mul_assoc, inv_mul_cancel_left' K0] at Hx2,
  simp only [← div_eq_inv_mul, sub_half, ← sub_le_iff_le_add'] at Hx2,
  simp only [sub_le_iff_le_add', div_le_iff' (zero_lt_two : (0:ℝ) < 2)] at Hx2,
  replace Hx2 := mul_le_mul_of_nonneg_left Hx2 K.coe_nonneg,
  simp only [mul_add, div_eq_inv_mul, add_comm φ,
    mul_inv_cancel_left' (two_ne_zero : (2:ℝ) ≠ 0), mul_inv_cancel_left' K0] at Hx2,
  refine hx1.trans _,
  simp only [mul_comm (2:ℝ) K, mul_assoc, hδφ, ← add_assoc, ← mul_add, add_le_add_iff_right],
  refine Hx2.trans _,
  simp only [add_le_add_iff_right],
  refine (mul_le_mul_of_nonneg_left _ K.coe_nonneg),
  refine (mul_le_mul_of_nonneg_left _ zero_le_two),
  refine le_trans (cond.h_bound_by _ _ le_rfl rfl _ _) _,
  refine mul_le_mul_of_nonneg_left (le_of_eq _) H.coe_nonneg,
  apply norm_res_of_eq,
  rw mul_assoc
end
.

end normed_spectral

open normed_spectral

/-- Proposition 9.6 in [Analytic] -/
theorem normed_spectral (m : ℕ) (c₀ H : ℝ≥0) [fact (0 < H)]
  (M : system_of_double_complexes.{u}) (k K k' : ℝ≥0)
  [fact (1 ≤ k)] [hK : fact (1 ≤ K)] [fact (k₀ m k ≤ k')] [fact (1 ≤ k')]
  (cond : M.normed_spectral_conditions m k K k' (ε m K) c₀ H) :
  (M.row 0).is_weak_bounded_exact (k' * k') (2 * K₀ m K * H) m c₀ :=
begin
  unfreezingI { revert M k K k' },
  induction m with m IH, { exact base c₀ H },
  dsimp [ε, k₀, K₀],
  introsI M k K k' _ _ _ _ cond,
  rw ← system_of_complexes.truncate_is_weak_bounded_exact_iff,
  { exact IH (truncate.obj M) (k*k*k) (K*(K*K+1)) k' cond.truncate },
  { refine IH M (k*k*k) (K*(K*K+1)) k' (cond.of_le (m.le_succ) _ _ le_rfl le_rfl le_rfl);
    apply_instance }
end

end system_of_double_complexes
