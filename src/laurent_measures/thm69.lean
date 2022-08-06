-- import for_mathlib.short_exact_sequence
import data.int.interval
import data.finset.nat_antidiagonal
import laurent_measures.aux_lemmas
import laurent_measures.basic
import laurent_measures.theta
import linear_algebra.basic
import order.filter.at_top_bot tactic.linarith
import for_mathlib.nnreal

/-!
This file introduces the maps
* `θ`, which is the specialization of evaluation-at-ξ map `ϑ` from `laurent_measures.theta`
  at `ξ=2⁻¹`.
* `ϕ` which corresponds to multiplying a Laurent series in `ℒ S = (laurent_measures r S)`
  for `r = 2^(1/p)` by `T⁻¹-2`.
* `ψ` corresponds to dividing a Laurent series by `(T⁻¹-2)`. It is defined only on series
  vanishing at `2⁻¹`, so that it again takes values in `ℒ S`
* The maps `Θ`, `Φ` and `Ψ` are the "measurifications" of `θ`, `ϕ` and `ψ`,
  so they are morphisms in the right category (**[FAE]** Not here any more!)

The main results are
* `injective_ϕ` stating that `ϕ` is injective;
* `θ_ϕ_complex` stating that `ϕ ∘ θ = 0`; and
* `θ_ϕ_exact` stating that the kernel of `θ` coincides with the image of `ϕ`.
Together with `ϑ_surjective` from `laurent_measures.theta` (specialized at `ξ=2⁻¹`, so that `ϑ` is
`θ`) this is the statement of Theorem 6.9 of `Analytic.pdf` of interest to us, although only "on
elements" and not yet as a Short Exact Sequence in the right category.
-/

noncomputable theory

open nnreal theta laurent_measures aux_thm69 finset
open_locale nnreal classical big_operators topological_space

section phi

parameter {r : ℝ≥0}

local notation `ℒ` := laurent_measures r
variables [fact (0 < r)]
variable {S : Fintype}

def ϕ : ℒ S → ℒ S :=
λ F, shift (1) F - 2 • F

lemma ϕ_apply (F : ℒ S) (s : S) (n : ℤ) : ϕ F s n = F s (n+1) - 2 * F s n :=
by simp only [ϕ, sub_apply, nsmul_apply, shift_to_fun_to_fun, nsmul_eq_mul]; refl

lemma ϕ_natural (S T : Fintype) (f : S ⟶ T) : --[fact (0 < p)] [fact ( p ≤ 1)] :
  ϕ ∘ laurent_measures.map_hom f = laurent_measures.map_hom f ∘ ϕ :=
begin
  ext F t n,
  simp only [ϕ, sum_sub_distrib, mul_sum, function.comp_app, map_hom_to_fun, sub_apply,
    nsmul_apply, shift_to_fun_to_fun,
    map_apply, nsmul_eq_mul, mul_ite, mul_zero], -- squeezed for time
end

-- #check @ϕ

-- lemma tsum_reindex (F : ℒ S) (N : ℤ) (s : S) : ∑' (l : ℕ), (F s (N + l) : ℝ) * (2 ^ l)⁻¹ =
--  2 ^ N * ∑' (m : {m : ℤ // N ≤ m}), (F s m : ℝ) * (2 ^ m.1)⁻¹ :=
-- begin
--   have h_shift := int_tsum_shift (λ n, (F s n : ℝ) * (2 ^ (-n))) N,
--   simp only at h_shift,
--   simp_rw [subtype.val_eq_coe, ← zpow_neg],
--   rw [← h_shift, ← _root_.tsum_mul_left, tsum_congr],
--   intro n,
--   rw [mul_comm (_ ^ N), mul_assoc, ← (zpow_add₀ (@two_ne_zero ℝ _ _)), neg_add_rev,
--     neg_add_cancel_comm, zpow_neg, zpow_coe_nat, add_comm],
-- end

variable [fact (r < 1)]

lemma injective_ϕ (F : ℒ S) (H : ϕ F = 0) : F = 0 :=
begin
  dsimp only [ϕ] at H, rw [sub_eq_zero] at H,
  replace H : ∀ n : ℤ, ∀ s : S, 2 * F s (n - 1) = F s n,
  { intros n s,
    rw laurent_measures.ext_iff at H,
    convert (H s (n-1)).symm using 1,
    { rw [two_smul, two_mul], refl, },
    { simp [shift] } },
  ext s n,
  apply int.induction_on' n (F.d - 1),
  { refine lt_d_eq_zero _ _ (F.d - 1) _,
    simp only [sub_lt_self_iff, zero_lt_one], },
  { intros k h hk₀,
    simp [← H (k + 1) s, add_sub_cancel, hk₀, mul_zero] },
  { intros k h hk₀,
    simpa only [hk₀, mul_eq_zero, bit0_eq_zero, one_ne_zero, false_or, zero_apply] using H k s }
end

lemma injective_ϕ' : function.injective (ϕ : ℒ S → ℒ S) :=
begin
  let PHI : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) :=
    shift (1) - 2 • comphaus_filtered_pseudo_normed_group_hom.id,
  apply (injective_iff_map_eq_zero (PHI.to_add_monoid_hom)).mpr,
  exact injective_ϕ
end

end phi

section mem_exact

parameter {p : ℝ≥0}

/-- `r`, or `r(p)`, is `2⁻ᵖ`. -/
def r : ℝ≥0 := 2⁻¹ ^ (p : ℝ)

lemma r_pos : 0 < r :=
suffices 0 < (2 : ℝ≥0)⁻¹ ^ (p : ℝ), by simpa [r],
rpow_pos (nnreal.inv_pos.mpr zero_lt_two)

instance r_pos' : fact (0 < r) := ⟨r_pos⟩

lemma r_coe : (2⁻¹ : ℝ) ^ (p : ℝ) = r :=
begin
  have : (2⁻¹ : ℝ) = ((2⁻¹ : ℝ≥0) : ℝ),
  simp only [one_div, nonneg.coe_inv, nnreal.coe_bit0, nonneg.coe_one],
  rw [this, ← nnreal.coe_rpow, nnreal.coe_eq],
  refl,
end

variable [fact(0 < p)]

lemma r_lt_one : r < 1 :=
begin
  refine rpow_lt_one two_inv_lt_one _,
  rw nnreal.coe_pos,
  exact fact.out _
end

instance r_lt_one' : fact (r < 1) := ⟨r_lt_one⟩

variable {S : Fintype}

local notation `ℒ` := laurent_measures r
local notation `ℳ` := real_measures p

theorem nnreal.rpow_int_cast (x : nnreal) (n : ℤ) : x ^ (n : ℝ) = x ^ n :=
begin
  apply subtype.ext,
  simp,
end

def θ : ℒ S → ℳ S := ϑ 2⁻¹ r p S

lemma θ_natural [fact (0 < p)] [fact (p ≤ 1)] (S T : Fintype) (f : S ⟶ T) (F : ℒ S) (t : T) :
  θ (map f F) t = real_measures.map f (θ F) t :=
begin
  simp only [θ, ϑ, one_div, map_apply, int.cast_sum, inv_zpow', zpow_neg, real_measures.map_apply],
  rw ← tsum_sum,
  { congr', ext n, exact sum_mul, },
  intros,
  rw mem_filter at H,
  rcases H with ⟨-, rfl⟩,
  have := F.summable i,
  refine summable.add_compl (_ : summable (_ ∘ (coe : {n : ℤ | 0 ≤ n} → ℤ))) _,
  { have moo := summable.comp_injective this
      (subtype.coe_injective : function.injective (coe : {n : ℤ | 0 ≤ n} → ℤ)),
    refine summable_of_norm_bounded _ (moo) _, clear moo this,
    rintro ⟨n, (hn : 0 ≤ n)⟩,
    simp only [function.comp_app, subtype.coe_mk, norm_mul, norm_inv, norm_zpow, real.norm_two],
    rw (F i n).norm_cast_real,
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
    delta r,
    delta r,
    rw (by push_cast : ((2 : ℝ) ^ n)⁻¹ = ((2 ^ n)⁻¹ : nnreal)),
    norm_cast,
    rw [← nnreal.rpow_int_cast, ← inv_rpow],
    rw nnreal.rpow_int_cast,
    set m := n.nat_abs with hm,
    have hmn : n = m := by { rw hm, exact int.eq_nat_abs_of_zero_le hn },
    rw hmn,
    norm_cast,
    apply pow_le_pow_of_le, clear hn hmn hm m n,
    apply nnreal.le_self_rpow' (two_inv_lt_one.le),
    norm_cast,
    exact fact.out _,
  },
  {
    obtain ⟨d, hd⟩ := exists_bdd_filtration (r_pos) (r_lt_one) F,
    apply summable_of_ne_finset_zero, -- missing finset
    swap, exact (finset.subtype _ (finset.Ico d 0)),
    rintros ⟨z, (hz : ¬ (0 ≤ z))⟩ hz2,
    simp only [subtype.coe_mk, mul_eq_zero, int.cast_eq_zero, inv_eq_zero],
    left,
    apply hd,
    simp only [mem_subtype, subtype.coe_mk, mem_Ico, not_and, not_le] at hz2,
    by_contra h,
    push_neg at h,
    apply hz,
    specialize hz2 h,
    push_neg at hz2,
    exact hz2 },
end

variables [fact (p < 1)]

lemma half_lt_r : 2⁻¹ < r :=
calc (2⁻¹:ℝ≥0)
    = 2⁻¹ ^ (1:ℝ) : (rpow_one (2⁻¹:ℝ≥0)).symm
... < r : rpow_lt_rpow_of_exponent_gt (begin rw nnreal.inv_pos, norm_num, end)
  (begin apply nnreal.inv_lt_one, norm_num end) $
(nnreal.coe_lt_coe.mpr (fact.out _)).trans_le (nnreal.coe_one).le

lemma one_lt_two_r : 1 < 2 * r :=
begin
  have := half_lt_r,
  have this2 : (2⁻¹ : ℝ) < r,
    assumption_mod_cast,
  rw inv_pos_lt_iff_one_lt_mul' at this2, assumption_mod_cast,
  norm_num,
end

lemma r_inv_lt_2 : r⁻¹ < 2 :=
begin
  rw ← inv_inv (2 : ℝ≥0),
  exact nnreal.inv_lt_inv (by norm_num) half_lt_r,
end

lemma laurent_measures.summable_half (F : ℒ S) (s : S) :
  summable (λ n, ((F s n) : ℝ) * 2⁻¹ ^ n) :=
aux_thm69.summable_smaller_radius F.d (F.summable s) (λ n hn, lt_d_eq_zero _ _ _ hn) half_lt_r

lemma θ_ϕ_complex (F : ℒ S) : (θ ∘ ϕ) F = 0 :=
begin
  have t0 : (2 : ℝ)⁻¹ ≠ 0 := inv_ne_zero two_ne_zero,
  funext s,
  convert_to ∑' (n : ℤ), ((F s (n + 1) - 2 * F s n) : ℝ) * 2⁻¹ ^ n = 0,
  { apply tsum_congr,
    intro b,
    field_simp [ϕ] },
  simp_rw [sub_mul],
  rw [tsum_sub, sub_eq_zero],
  -- old proof was slicker :-(
  { refine tsum_eq_tsum_of_ne_zero_bij (λ i, (i.val : ℤ) - 1) _ _ _,
    { rintros ⟨x, _⟩ ⟨y, _⟩ h, dsimp at *, linarith },
    { rintros x hx,
      refine ⟨⟨x + 1, _⟩, _⟩,
      { rw function.mem_support at ⊢ hx,
        convert hx using 1,
        simp [zpow_add₀],
        ring },
      { simp } },
    { rintro ⟨i, hi⟩,
      simp [zpow_sub₀],
      ring } },
  { rw ← (equiv.add_group_add (-1 : ℤ)).summable_iff,
    simp only [function.comp, one_div, inv_zpow', equiv.add_group_add_apply,
      neg_add_cancel_comm],
    convert summable.mul_right 2 (F.summable_half s),
    ext x,
    simp [zpow_add₀], ring },
  { simp_rw [mul_assoc],
    convert (F.summable_half s).mul_left 2 },
end
.

/-!

### Definition of ψ

This involves dividing by T⁻¹ - 2 and we have to check that this process converges.
The proof below is pretty icky. It's "do some trivial rearrangements and it boils
down to the fact that you can interchange the order of summation in a ℝ≥0-valued
sum of sums"

-/

lemma nnreal.summable_mul_left_iff {X : Type*} {f : X → ℝ≥0} {a : ℝ≥0} (ha : a ≠ 0) :
summable f ↔ summable (λ (x : X), a * f x) :=
begin
  rw [← nnreal.summable_coe, ← nnreal.summable_coe],
  rw summable_mul_left_iff (by exact_mod_cast ha : (a : ℝ) ≠ 0),
  apply summable_congr,
  intro b,
  norm_cast,
end

lemma psi_def_summable {S : Fintype} (n : ℕ)
  (F : ℒ S)
  (s : S) :
  summable
    (λ (k : ℕ),
       r ^ (F.d + ↑n) *
         (2⁻¹ ^ (k : ℤ) * ∥F s (F.d + ↑n + ↑k)∥₊)) :=
begin
  have := F.summable_half s,
  apply summable.mul_left,
  have h : (2⁻¹ : ℝ≥0) ≠ 0 := by norm_num,
  rw nnreal.summable_mul_left_iff (show ((2⁻¹ : ℝ≥0) ^ (F.d + n) ≠ 0), from zpow_ne_zero _ h),
  simp only [← mul_assoc, ← zpow_add₀ h],
  have this2 := lt_d_eq_zero F s,
  rw ← summable_norm_iff at this,
  simp_rw ← _root_.coe_nnnorm at this,
  rw summable_coe at this,
  rw nnreal.summable_iff_on_nat_less_shift F.d _ (F.d + n) at this,
  { convert this,
    ext1 k,
    rw mul_comm,
    simp only [inv_zpow', neg_add_rev, nnnorm_mul, nnnorm_zpow, real.nnnorm_two],
    congr' },
  { intros n hn,
    simp [this2 n hn] },
end

lemma psi_def_summable2 {S : Fintype}
  [fact (0 < p)]
  [fact (p < 1)]
  (F : ℒ S)
  (s : ↥S) :
  ∀ (k : ℕ),
    summable
      (λ (n : ℕ),
         r ^ (F.d + ↑n) *
           ((2⁻¹ : ℝ≥0) ^ (k : ℤ) * ∥F s (F.d + ↑n + ↑k)∥₊)) :=
begin
  intro k,
  have hhalf : (2⁻¹ : ℝ≥0) ≠ 0, by norm_num,
  have hhalf' : (2⁻¹ : ℝ≥0) ≠ 0, by norm_num,
  have hr : r ≠ 0 := r_pos.ne.symm,
  rw nnreal.summable_mul_left_iff
    (show (2⁻¹ : ℝ≥0) ^ (-(k : ℤ)) * r ^ (k : ℤ) ≠ 0, from mul_ne_zero (zpow_ne_zero _ hhalf') (zpow_ne_zero _ hr)),
  have : ∀ x : ℕ, 2⁻¹ ^ -(k : ℤ) * r ^ (k : ℤ) * (r ^ (F.d + ↑x) * (2⁻¹ ^ (k : ℤ) * ∥F s (F.d + ↑x + ↑k)∥₊))
    = r ^ (F.d + x + k) * ∥F s (F.d + ↑x + ↑k)∥₊,
  { intro x,
    rw (show (2⁻¹ : ℝ≥0) ^ -(k : ℤ) * r ^ (k : ℤ) * (r ^ (F.d + ↑x) * (2⁻¹ ^ (k : ℤ) * ∥F s (F.d + ↑x + ↑k)∥₊))
      = (2⁻¹ : ℝ≥0) ^ -(k : ℤ) * 2⁻¹ ^ (k : ℤ) * r ^ (k : ℤ) * r ^ (F.d + ↑x) *  ∥F s (F.d + ↑x + ↑k)∥₊, by ring),
    simp only [zpow_add₀ hr, ← zpow_add₀ hhalf'],
    simp,
    left,
    ring,
    },
  rw summable_congr this, clear this,
  have := F.summable' s,
  rw nnreal.summable_iff_on_nat_less_shift F.d _ (F.d + k) at this,
  { convert this,
    ext n,
    rw [mul_comm, add_right_comm],
    refl },
  { intros n hn,
    convert zero_mul _,
    convert nnnorm_zero,
    exact lt_d_eq_zero F s n hn },
end

lemma psi_def_summable3 {S : Fintype}
  [fact (0 < p)]
  [fact (p < 1)]
  (F : ℒ S)
  (s : ↥S) :
  summable
    (λ (k : ℕ),
       ∑' (n : ℕ),
         r ^ (F.d + ↑n) *
           (2⁻¹ ^ (k : ℤ) * ∥F s (F.d + ↑n + ↑k)∥₊)) :=
begin
  -- take 2⁻¹^k out the tsum,
  -- put r^k into the tsum,
  -- bounded by sum of GP,
  have bdd : ∀ k : ℕ, ∑' (n : ℕ),
         r ^ (F.d + ↑n + k) * ∥F s (F.d + ↑n + ↑k)∥₊ ≤
           ∑' (t : ℤ),
         r ^ t * ∥F s t∥₊,
  { intro k,
    simp_rw add_right_comm,
    have hinj : function.injective (λ (m : ℕ), F.d + k + m),
    { rintros a b (h2 : F.d + k + a = F.d + k + b),
      simpa using h2 },
      refine tsum_le_tsum_of_inj _ hinj _ _ _ _,
      { intros, apply zero_le' },
      { intro, refl },
      { rw ← @nnreal.summable_iff_on_nat_less_shift (λ (z : ℤ), r ^ z * ∥F s z∥₊) F.d _ (F.d + k),
        { convert F.summable' s,
          ext z,
          rw mul_comm,
          refl },
        { intros n hn,
          simp [lt_d_eq_zero F s n hn] } },
      { convert F.summable' s,
        ext z,
        rw mul_comm,
        refl } },
  have : ∀ k : ℕ, ∑' (n : ℕ), r ^ (F.d + ↑n) * (2⁻¹ ^ (k : ℤ) * ∥F s (F.d + ↑n + ↑k)∥₊) =
   (∑' (n : ℕ), r ^ (F.d + ↑n + k) * (∥F s (F.d + ↑n + ↑k)∥₊)) * (2⁻¹ * r⁻¹) ^ (k : ℤ),
  { intro k,
    rw ← nnreal.tsum_mul_right,
    apply tsum_congr,
    intro n,
    simp only [zpow_add₀ r_pos.ne.symm, zpow_coe_nat, one_div, inv_pow, div_zpow],
    have foo : (2 * r) ^ k ≠ 0,
    { apply pow_ne_zero, apply mul_ne_zero,
      { norm_num },
      { exact r_pos.ne.symm },

    },
    field_simp [foo],
    rw mul_pow,
    ring, },
  rw summable_congr this, clear this,
  suffices : summable (λ k : ℕ, (∑' (t : ℤ), r ^ t * ∥F s t∥₊) * (2⁻¹ * r⁻¹) ^ k),
  { refine summable_of_le _ this,
    intro k,
    rw zpow_coe_nat,
    apply nnreal.mul_le_mul_right (bdd k),
  },
  apply summable.mul_left,
  apply summable_geometric,
  exact div_lt_one_of_lt half_lt_r,
end



lemma psi_def_aux_4 {S : Fintype} [fact (0 < p)] [fact (p < 1)] (F : ℒ S) (s : ↥S) : summable
  (λ (m : ℕ),
     ∥(2 : ℝ) ^ (F.d + ↑m)∥₊ *
       ((∑' (k : ℕ), ∥F s (F.d + ↑m + ↑k)∥₊ * 2⁻¹ ^ (F.d + ↑m + ↑k)) * r ^ (F.d + ↑m))) :=
begin
  -- tidy up
  simp_rw [nnnorm_zpow, real.nnnorm_two],
  have : ∀ m : ℕ, (2 : ℝ≥0) ^ (F.d + ↑m) *
  ((∑' (k : ℕ), ∥F s (F.d + ↑m + ↑k)∥₊ * 2⁻¹ ^ (F.d + ↑m + ↑k)) * r ^ (F.d + ↑m)) =
  ∑' (k : ℕ), (2 : ℝ≥0) ^ (F.d + ↑m) * ∥F s (F.d + ↑m + ↑k)∥₊ * 2⁻¹ ^ (F.d + ↑m + ↑k) * r ^ (F.d + ↑m),
  { intro m,
    rw [← nnreal.tsum_mul_right, ← nnreal.tsum_mul_left],
    apply tsum_congr,
    intro b,
    ring },
  rw summable_congr this, clear this,
  -- TODO : maybe now is the time to tidy up a bit (e.g. cancel the 2^x and 2⁻¹^x)
  suffices : summable
  (λ (m : ℕ), ∑' (k : ℕ),
       ∥F s (F.d + ↑m + ↑k)∥₊ *
       2⁻¹ ^ (k : ℤ) * r ^ (F.d + ↑m)),
  { refine (summable_congr _).2 this,
    intro m,
    apply tsum_congr,
    intro b,
    rw [inv_zpow , inv_zpow],
    rw [← zpow_neg, ←zpow_neg],
    have h2 : (2 : ℝ≥0) ≠ 0 := two_ne_zero,
    simp only [zpow_add₀, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff, zpow_coe_nat, neg_add_rev, zpow_neg,
  mul_eq_mul_right_iff],
    field_simp [zpow_ne_zero _ h2], left,
    ring,
  },
  simp_rw [mul_comm],
  -- change order of summation
  apply nnreal.summable_symm,
  -- check various things are summable
  have := F.summable_half s,
  { intro n,
    apply psi_def_summable },
  { apply psi_def_summable2 },
  -- sum is then bounded above by a GP.
  { apply psi_def_summable3, },
end

lemma psi_def_aux_3 {S : Fintype} [fact (0 < p)] [fact (p < 1)] (F : ℒ S) (s : ↥S) : summable
  (λ (n : ℤ),
     ∥-(2 : ℝ) ^ (n - 1)∥₊ *
       ite (F.d ≤ n) ((∑' (k : ℕ), ∥F s (n + ↑k)∥₊ * 2⁻¹ ^ (n + ↑k)) * r ^ n) 0) :=
begin
  -- get rid of factor of -2⁻¹
  simp_rw [_root_.nnnorm_neg, zpow_sub₀ (two_ne_zero : (2 : ℝ) ≠ 0), nnnorm_div, zpow_one,
    div_eq_mul_inv _ ∥(2 : ℝ)∥₊, mul_comm _ ∥(2 : ℝ)∥₊⁻¹, mul_assoc],
  apply summable.mul_left,
  have hinj : function.injective (λ (m : ℕ), F.d + m),
  { rintros a b (h2 : F.d + a = F.d + b),
    simpa using h2 },
  -- change outer sum to m : ℕ with n : ℤ = F.d + m
  suffices : summable (λ (m : ℕ),
     ∥(2 : ℝ) ^ (F.d + m)∥₊ *
       ((∑' (k : ℕ), ∥F s (F.d + m + ↑k)∥₊ * 2⁻¹ ^ (F.d + m + ↑k)) * r ^ (F.d + m))),
  refine nnreal.summable_of_comp_injective hinj _ _,
  { intros a ha,
    rw [if_neg], simp,
    intro hda, apply ha,
    use (a - F.d).to_nat,
    simp, rw int.to_nat_of_nonneg, ring, linarith },
  { refine (summable_congr _).1 this,
    simp },
  exact psi_def_aux_4 F s,
end

lemma psi_def_aux_2 {S : Fintype} [fact (0 < p)] [fact (p < 1)] (F : ℒ S) (s : ↥S) : summable
  (λ (n : ℤ),
     ite (F.d ≤ n) ∥-(2 : ℝ) ^ (n - 1) * ∑' (k : ℕ), ↑(F s (n + ↑k)) * 2⁻¹ ^ (n + ↑k) * r ^ n∥₊ 0) :=
begin
  simp_rw [nnnorm_mul],
  -- next : put norm inside inner tsum (a one way implication)
  suffices : summable
  (λ (n : ℤ), ∥-(2 : ℝ) ^ (n - 1)∥₊ *
     ite (F.d ≤ n)
     ((∑' (k : ℕ), ∥F s (n + ↑k)∥₊ * 2⁻¹ ^ (n + ↑k)) * r ^ n)
       0),
  refine summable_of_le _ this,
  { intro n,
    split_ifs,
    { simp only [_root_.nnnorm_neg, nnnorm_zpow, real.nnnorm_two, one_div, inv_zpow', neg_add_rev],
      refine mul_le_mul_of_nonneg_left _ _,
      { refine le_trans (nnnorm_tsum_le _) _,
        { clear this, have := F.summable_half s,
          simp_rw nnnorm_mul,
          apply summable.mul_right,
          rw ← summable_norm_iff at this,
          simp_rw ← _root_.coe_nnnorm at this,
          rw nnreal.summable_coe at this,
          have hinj : function.injective (λ (b : ℕ), n + b),
          { rintros a b (h2 : n + a = n + b),
            simpa using h2 },
            convert summable_comp_injective this hinj,
            ext1 k,
            simp [← zpow_neg] },
        { rw ← nnreal.tsum_mul_right,
          apply le_of_eq,
          apply tsum_congr,
          { intro k,
            simp only [nnnorm_mul, nnnorm_zpow, real.nnnorm_two, nnnorm_eq, mul_eq_mul_right_iff],
            left, left,
            congr } } },
      { simp } },
    { simp } },
  exact psi_def_aux_3 _ _,
end

lemma psi_def_aux {S : Fintype} [fact (0 < p)] [fact (p < 1)] (F : ℒ S) (s : ↥S) :
  summable (λ (n : ℤ), ∥ite (F.d ≤ n) (-(2 : ℝ) ^ (n - 1) *
    ∑' (k : ℕ), ↑(F s (n + ↑k)) * 2⁻¹ ^ (n + ↑k)) 0∥₊ * r ^ n) :=
begin
  suffices :  summable (λ (n : ℤ), ite (F.d ≤ n) ∥-(2 : ℝ) ^ (n - 1) *
    ∑' (k : ℕ), ↑(F s (n + ↑k)) * 2⁻¹ ^ (n + ↑k) * r ^ n∥₊ 0),
  refine summable_of_le _ this,
  { intro n,
    split_ifs,
    { apply le_of_eq,
      simp_rw _root_.tsum_mul_right,
      rw [ ← mul_assoc, nnnorm_mul _ ((r : ℝ) ^ n)],
      simp },
    { simp } },
  exact psi_def_aux_2 _ _,
end

def ψ (F : ℒ S) (hF : θ F = 0) : ℒ S :=
{ to_fun := λ s n, if F.d ≤ n then
    ∑ l in range (n - F.d).nat_abs.succ, F s (n - 1 - l) * (2 ^ l)
    else 0,
  summable' := λ s, begin
    -- make everything real
    change summable (λ (n : ℤ),
     ∥((ite (F.d ≤ n)
       (∑ (l : ℕ) in range (n - F.d).nat_abs.succ, F s (n - 1 - ↑l) * 2 ^ l) 0 : ℤ) : ℝ)∥₊
     * r ^ n),
    push_cast,
    -- hypothesis that infinite sum converges at r>2⁻¹
    -- get hypothesis that infinite sum is 0 at 2⁻¹
    simp only [θ, ϑ] at hF,
    replace hF := congr_fun hF s, dsimp at hF,
    -- change sum from ℤ to ℕ
    --rw nnreal.summable_iff_on_nat_less F.d, swap,
    --{ intros n hn, simp [if_neg hn.not_le] },
    have h1 : ∀ (n : ℤ),
      ite (F.d ≤ n) (∑ (l : ℕ) in range (n - F.d).nat_abs.succ, (F s (n - 1 - ↑l) : ℝ) * 2 ^ l) 0 =
      ite (F.d ≤ n) (-(2 : ℝ)^(n-1)*∑' (k : ℕ), F s (n + k) * 2⁻¹ ^ (n + k)) 0,
    { intro n,
      split_ifs with hn, swap, refl,
      rw [← inv_mul_eq_iff_eq_mul₀, ← neg_inv, neg_mul, mul_sum, neg_eq_iff_add_eq_zero, ← hF],
        swap, exact neg_ne_zero.2 (zpow_ne_zero _ two_ne_zero),
      convert @tsum_add_tsum_compl ℝ ℤ _ _ _ _ _ {x : ℤ | x < n}
        (summable.subtype (F.summable_half s) _) (summable.subtype (F.summable_half s) _) using 2,
      { simp_rw [← inv_zpow, mul_comm ((2⁻¹ : ℝ)^(n-1)), mul_assoc],
        simp_rw (show ∀ (x : ℕ), (2 : ℝ)^x = 2⁻¹^(-(x : ℤ)), by {intros, simp}),
        simp_rw [← zpow_add₀ (by norm_num : (2⁻¹ : ℝ) ≠ 0), add_comm, ← sub_eq_add_neg],
        rw ← tsum_eq_sum,
        convert @equiv.tsum_eq ℝ _ _ _ _ _
          (⟨λ m, ⟨n - 1 - m, lt_of_le_of_lt (sub_le_self _ (int.coe_zero_le m)) (sub_one_lt n)⟩,
           (λ z, (n - 1 - z.1).nat_abs), λ m, by simp, λ ⟨z, hz⟩, subtype.ext begin
--             squeeze_simp,
             change n - 1 - (n - 1 - z).nat_abs = z,
             rw ← int.eq_nat_abs_of_zero_le (sub_nonneg_of_le (int.le_sub_one_of_lt hz)),
             ring, end⟩ : ℕ ≃ {z : ℤ // z < n}) _,
        { ext, refl },
        { intros b hb,
          rw mul_eq_zero, left,
          norm_cast,
          apply lt_d_eq_zero,
          by_contra h, push_neg at h, apply hb,
          rw [mem_range, nat.succ_eq_add_one, ← int.coe_nat_lt, int.coe_nat_add,
            ← int.eq_nat_abs_of_zero_le]; linarith } },
      { convert @equiv.tsum_eq ℝ _ _ _ _ _
          (⟨λ x, ⟨n + x, (int.le.intro rfl).not_lt⟩, (λ z, (z.1 - n).nat_abs),
            λ x, by simp, λ ⟨x, hx⟩, subtype.ext begin
              change n + _ = x,
              rw ← int.eq_nat_abs_of_zero_le (sub_nonneg.2 (le_of_not_lt hx)),
              exact add_eq_of_eq_sub' rfl,
            end⟩ : ℕ ≃ {z : ℤ // ¬ z < n}) _,
        ext, refl },
    },
    suffices : summable (λ (n : ℤ),
     ∥ite (F.d ≤ n) (-(2 : ℝ)^(n-1)*∑' (k : ℕ), ↑(F s (n + k)) * 2⁻¹ ^ (n + k)) 0∥₊ *
       r ^ n),
    { refine (summable_congr _).2 this,
      intro n,
      congr' 2,
      apply h1 n,
    }, clear h1,
    clear hF,
    exact psi_def_aux F s,
  end }

theorem θ_ϕ_split_exact (F : ℒ S) (hF : θ F = 0) : ϕ (ψ F hF) = F :=
begin
  ext s n,
  simp only [ϕ, ψ, sub_apply, shift_to_fun_to_fun, laurent_measures.coe_mk, nsmul_apply,
    nsmul_eq_mul, int.coe_nat_succ, int.coe_nat_zero, zero_add],
  split_ifs with h1 h2,
  { rw [sum_range_succ', (by norm_num : (1 : ℤ) + 1 = 2), mul_sum],
    convert add_sub_cancel' _ _,
    { rw [nat.succ_eq_add_one, (by ring : n + 1 - F.d = n - F.d + 1)],
      obtain ⟨m, hm⟩ := (int.eq_coe_of_zero_le (sub_nonneg.mpr h2)),
      rw hm,
      norm_cast },
    { ext,
      push_cast,
      ring_exp,
      congr' 2,
      ring },
    { simp } },
  { have hF : F.d = n + 1, linarith,
    simp [hF] },
  { linarith },
  { exact (lt_d_eq_zero F s n (not_le.mp h)).symm },
end

theorem θ_ϕ_exact (F : ℒ S) (hF : θ F = 0) : ∃ G, ϕ G = F :=
⟨ψ F hF, θ_ϕ_split_exact F hF⟩

end mem_exact
