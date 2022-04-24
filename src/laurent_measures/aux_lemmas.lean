import data.finset.nat_antidiagonal
import analysis.normed_space.basic
import analysis.specific_limits.basic
import laurent_measures.int_nat_shifts

noncomputable theory

open metric finset normed_field --filter
open_locale nnreal classical big_operators topological_space

namespace aux_thm69

section equivalences_def

-- for mathlib?
def range_equiv_Icc {n d : ℤ} (m : ℕ) (hm : n - d = m) :
  range m.succ ≃ (Icc d n) :=
begin
  refine ⟨λ a, ⟨a + d, mem_Icc.mpr ⟨_, _⟩⟩, _, _, _⟩,
  { exact (le_add_iff_nonneg_left _).mpr (int.of_nat_nonneg _) },
  { refine add_le_of_le_sub_right _,
    exact (int.coe_nat_le.mpr (nat.le_of_lt_succ $ (@mem_range m.succ a).mp a.2)).trans hm.ge },
  { rintro ⟨a, hha⟩,
    refine ⟨(a - d).nat_abs, mem_range_succ_iff.mpr _⟩,
    lift (a - d) to ℕ using (sub_nonneg.mpr ((mem_Icc).mp hha).1) with ad had,
    rw [int.nat_abs_of_nat, ← (int.coe_nat_le_coe_nat_iff _ _), had, ← hm],
    exact sub_le_sub_right ((mem_Icc).mp hha).2 _ },
  { exact λ x, subtype.ext (by simp) },
  { rintro ⟨x, hx⟩,
    simp [int.nat_abs_of_nonneg (sub_nonneg.mpr (mem_Icc.mp hx).1), sub_add_cancel] }
end

--for `mathlib`?
def equiv_bdd_integer_nat (N : ℤ) : ℕ ≃ {x // N ≤ x} :=
{ to_fun := λ n, ⟨n + N, le_add_of_nonneg_left (int.coe_nat_nonneg n)⟩,
  inv_fun := λ x, (x.1 - N).nat_abs,
  left_inv := λ n, by simp,
  right_inv := λ ⟨x, hx⟩, subtype.ext (by simp [int.nat_abs_of_nonneg (sub_nonneg.mpr hx)]) }

def equiv_Icc_bdd_nonneg {d : ℤ} (hd : 0 ≤ d) : {x // d ≤ x} ≃
  {x // x ∉ range (int.eq_coe_of_zero_le hd).some}:=
begin
  fconstructor,
  { rintro ⟨_, h⟩,
    have := (int.eq_coe_of_zero_le (hd.trans h)).some_spec,
    rw [(int.eq_coe_of_zero_le hd).some_spec, this, int.coe_nat_le, ← not_lt, ← mem_range] at h,
    exact ⟨_, h⟩ },
  { rintro ⟨_, h⟩,
    rw [mem_range, nat.lt_iff_add_one_le, not_le, nat.lt_add_one_iff, ← int.coe_nat_le,
      ← (int.eq_coe_of_zero_le hd).some_spec] at h,
    exact ⟨_, h⟩ },
  { rintro ⟨_, h⟩,
    simp only [int.coe_nat_inj', int.of_nat_eq_coe],
    exact (int.eq_coe_of_zero_le (hd.trans h)).some_spec.symm },
  { rintro ⟨_, h⟩,
    simp only [int.coe_nat_inj', int.of_nat_eq_coe],
    exact ((@exists_eq' _ _).some_spec).symm },
end

def T {d : ℤ} (hd : d < 0) : finset {x : ℤ // d ≤ x} := Ico ⟨d, le_of_eq rfl⟩ ⟨0, le_of_lt hd⟩

lemma T.zero_le {d : ℤ} (hd : d < 0) {y : {x // d ≤ x}} (h : y ∉ T hd) :
  0 ≤ y.1 :=
suffices (⟨d, rfl.le⟩ : {x // d ≤ x}) ≤ y → (⟨_, hd.le⟩ : {x // d ≤ x}) ≤ y, from this y.2,
by { simpa [T, hd] using h }

def R {d n : ℤ} (hn : 0 ≤ n - d) : finset {x : ℤ // d ≤ x} := Icc ⟨d, le_of_eq rfl⟩ ⟨n, int.le_of_sub_nonneg hn⟩

def equiv_Icc_R {d n : ℤ} (hn : 0 ≤ n - d) : Icc d n ≃ R hn :=
begin
  fconstructor,
  { rintro ⟨m, hm⟩,
    replace hm := mem_Icc.mp hm,
    use ⟨m, hm.1⟩,
    dsimp [R],
    rw mem_Icc,
    use and.intro (subtype.mk_le_mk.mpr hm.1) (subtype.mk_le_mk.mpr hm.2) },
  { dsimp [R],
    rintro ⟨⟨x, hx⟩, h⟩,
    rw mem_Icc at h,
    use x,
    rw mem_Icc,
    use and.intro hx (subtype.mk_le_mk.mp h.2) },
  { simp only [id.def],
    rintro ⟨⟨x, hx⟩, h⟩,
    all_goals {simp only}, },
  { simp only [id.def],
    dsimp [R],
    rintro ⟨⟨x, hx⟩, h⟩,
    simp only },
end

def equiv_compl_R_bdd {d n : ℤ} (hn : 0 ≤ n - d): {a : ℤ // n.succ ≤ a } ≃
  ((R hn)ᶜ : set {x : ℤ // d ≤ x}) :=
begin
  fconstructor,
  { rintro ⟨m, hm⟩,
    have hd : d ≤ m := (int.le_add_one (int.le_of_sub_nonneg hn)).trans hm,
    use ⟨m, hd⟩,
    dsimp only [R],
    simpa [mem_coe, set.mem_compl_eq, mem_Icc, subtype.mk_le_mk, not_and, hd, forall_true_left, not_le, int.lt_iff_add_one_le, hm] },
  { rintro ⟨⟨x, hx⟩, h_mem⟩,
    dsimp only [R] at h_mem,
    simp only [subtype.mk_le_mk, coe_Icc, not_and, not_le, set.mem_compl_eq, set.mem_Icc, hx, forall_true_left, int.lt_iff_add_one_le] at h_mem,
    use ⟨x, h_mem⟩ },
  { rintro ⟨_, _⟩, simp only [id.def] },
  { rintro ⟨⟨_, _⟩, _⟩, simpa }
end

end equivalences_def

section equivalences_lemma

--for mathlib?
lemma sum_reverse {β : Type*} [add_comm_group β] (f : ℤ → β) (n : ℕ) :
  ∑ l in (range n.succ), (f (n - l)) = ∑ l in (range n.succ), f l :=
begin
  induction n with n hn generalizing f,
  { simp only [zero_sub, int.coe_nat_zero, sum_singleton, neg_zero, range_one] },
  { rw [sum_range_succ', sum_range_succ (f ∘ coe)],
    simp only [←hn, int.coe_nat_zero, add_sub_add_right_eq_sub, function.comp_app, sub_zero,
      int.coe_nat_succ] }
end

lemma sum_range_sum_Icc' {α : Type*} [field α] (f : ℤ → α) {n d : ℤ} (hn : 0 ≤ n - d) :
 ∑ l in (range (int.eq_coe_of_zero_le hn).some.succ), (f (n - l)) * 2 ^ l =
 ∑ k in (Icc d n), (f k) * 2 ^ (n - k) :=
begin
  let m := (int.eq_coe_of_zero_le hn).some,
  have h := (int.eq_coe_of_zero_le hn).some_spec.symm,
  have sum_swap : ∑ (l : ℕ) in range m.succ, f (n - l) * 2 ^ l =
    ∑ (l : ℕ) in range m.succ, f (l + d) * 2 ^ (m - l),
  { convert (sum_reverse (λ l, f (n - l) * 2 ^ l) m).symm using 1,
    { simp_rw ← zpow_coe_nat },
    refine sum_congr rfl (λ x hx, _),
    congr' 1,
    { rw [sub_sub_assoc_swap, add_comm n, add_sub_assoc],
      exact congr_arg f ((add_right_inj _).mpr (eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq'.mp h))) },
    { simp only [← zpow_of_nat, int.of_nat_eq_coe, ← int.sub_nat_nat_eq_coe, int.sub_nat_nat_of_le
        (nat.lt_succ_iff.mp (mem_range.mp hx))] } },
  rw [sum_swap, ← sum_finset_coe, ← sum_finset_coe _ (Icc _ _)],
  refine fintype.sum_equiv (range_equiv_Icc _ h.symm) _ _ (λ x, _),
  dsimp [range_equiv_Icc],
  rw [← sub_sub, sub_right_comm, ← zpow_coe_nat],
  refine congr_arg ((*) _) (congr_arg (pow 2) _),
  have := @nat.cast_sub ℤ _ _ _ _ (mem_range_succ_iff.mp x.2),
  simpa only [this, h, int.nat_cast_eq_coe_nat, sub_left_inj, subtype.val_eq_coe],
end

lemma sum_range_sum_Icc (f : ℤ → ℝ) (n d : ℤ) (hn : 0 ≤ n - d) :
 ∑ l in (range (int.eq_coe_of_zero_le hn).some.succ), (f (n - l)) * 2 ^ l =
 ∑ k in (Icc d n), (f k) * 2 ^ (n - k) :=
sum_range_sum_Icc' f hn


lemma equiv_Icc_bdd_nonneg_apply {d : ℤ} (hd : 0 ≤ d) (x : {x // d ≤ x}) :
  ((equiv_Icc_bdd_nonneg hd x) : ℤ) = x.1 :=
begin
  rcases x with ⟨_, h⟩,
  exact (Exists.some_spec (int.eq_coe_of_zero_le (hd.trans h))).symm,
end

lemma equiv_Icc_R_apply {d n : ℤ} (hn : 0 ≤ n - d) (x : Icc d n) : ((equiv_Icc_R hn x) : ℤ) =
  (x : ℤ) := by {rcases x, refl}

lemma equiv_compl_R_bdd_apply {d n : ℤ} (hn : 0 ≤ n - d) (x : {a : ℤ // n.succ ≤ a }) :
(equiv_compl_R_bdd hn x : ℤ) = (x : ℤ) := by {rcases x with ⟨y, hy⟩, simpa}

lemma sum_Icc_sum_tail (f : ℤ → ℤ) (n d : ℤ)
  (hf : (has_sum (λ x : ℤ, (f x : ℝ) * (2 ^ x)⁻¹) 0))
  (hd : ∀ n : ℤ, n < d → f n = 0)
  (hn : 0 ≤ n - d) : - ∑ k in (Icc d n), ((f k) : ℝ) * 2 ^ (n - k) =
  2 ^ n * tsum (λ x : {a : ℤ // n.succ ≤ a }, (f x : ℝ) * (2 ^ x.1)⁻¹) :=
begin
  simp_rw [zpow_sub₀ (@two_ne_zero ℝ _ _), div_eq_mul_inv, ← mul_assoc, (mul_comm _ ((2 : ℝ) ^ n)), mul_assoc, ← mul_sum, neg_mul_eq_mul_neg, mul_eq_mul_left_iff],
  apply or.intro_left,
  have H_supp : function.support (λ n : ℤ, (f n  : ℝ) * (2 ^ n)⁻¹) ⊆ { a : ℤ | d ≤ a},
  { rw function.support_subset_iff,
    intro _,
    rw [← not_imp_not, not_not, mul_eq_zero],
    intro hx,
    simp only [not_le, set.mem_set_of_eq] at hx,
    apply or.intro_left,
    exact int.cast_eq_zero.mpr (hd _ hx), },
  rw ← (@has_sum_subtype_iff_of_support_subset ℝ ℤ _ _ (λ n : ℤ, ( f n ) * (2 ^ n)⁻¹) _ _ H_supp) at hf,
  let g := (λ n : {x : ℤ // d ≤ x}, ( f n : ℝ) * (2 ^ n.1)⁻¹),
  have hg : has_sum g 0 := hf,
  have := @sum_add_tsum_compl _ _ _ _ _ g _ (R hn) hg.summable,
  rw [hg.tsum_eq, add_eq_zero_iff_eq_neg] at this,
  replace this := neg_eq_iff_neg_eq.mpr this.symm,
  convert this using 1,
  { simp only [neg_inj],
    have h_R := @fintype.sum_equiv (Icc d n) (R hn) _ _ _ _ (equiv_Icc_R hn) ((λ x : ℤ, ((f x : ℝ) * (2 ^ x)⁻¹)) ∘ coe) (g ∘ coe),
    rw @sum_subtype ℝ ℤ _ (∈ Icc d n) _ (Icc d n) _ (λ x, ((f x) : ℝ) * (2 ^x)⁻¹),
    rw @sum_subtype ℝ _ _ (∈ R hn) _ (R hn) _ (λ x, g x),
    simp only,
    refine h_R _,
    { intro x,
      dsimp [g],
      rw [← coe_coe, equiv_Icc_R_apply hn x] },
    all_goals { intro _, refl } },
  { dsimp only [g],
    refine eq.trans _ (@equiv.tsum_eq _ _ _ _ _ _ (equiv_compl_R_bdd hn) (λ x, (f x : ℝ) * (2 ^ (x.1 : ℤ))⁻¹)),
    apply tsum_congr,
    intro x,
    simp_rw [← coe_coe],
    nth_rewrite_rhs 0 [subtype.val_eq_coe],
    rw [← coe_coe, equiv_compl_R_bdd_apply hn x, ← subtype.val_eq_coe], }
end

end equivalences_lemma

section summability

lemma summable_shift (f : ℤ → ℝ) (N : ℤ) :
  summable (λ x : ℕ, f (x + N)) ↔ summable (λ x : {x // N ≤ x}, f x) :=
@equiv.summable_iff _ _ _ _ _ (λ x : {x // N ≤ x}, f x) (equiv_bdd_integer_nat N)


lemma int_tsum_shift (f : ℤ → ℝ) (N : ℤ) :
  ∑' (x : ℕ), f (x + N) = ∑' (x : {x // N ≤ x}), f x :=
begin
  apply tsum_eq_tsum_of_has_sum_iff_has_sum,
  intro _,
  apply (@equiv.has_sum_iff ℝ _ ℕ _ _ (f ∘ coe) _ ((equiv_bdd_integer_nat N))),
end

lemma summable_of_eventually_zero (f : ℤ → ℝ) (d : ℤ) (hd : ∀ (n : ℤ), n < d → f n = 0) :
  summable (λ (n : ℕ), f (-↑n - 1)) :=
begin
  refine summable_of_norm_bounded_eventually _ summable_zero _,
  suffices : {x : ℕ | ¬f (-↑x - 1) = 0}.finite, by simpa,
  apply (range (int.to_nat (-d))).finite_to_set.subset _,
  refine λ x h, mem_coe.mpr (mem_range.mpr (int.lt_to_nat.mpr (not_le.mp (λ H, _)))),
  simpa [hd _ (int.sub_one_lt_iff.mpr (neg_le.mp H))] using h,
end

lemma summable_iff_on_nat_less {f : ℤ → ℝ} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
  summable f ↔ summable (λ n : ℕ, f n) :=
int_summable_iff.trans $ and_iff_left_iff_imp.mpr $ λ hh, summable_of_eventually_zero f d $
  λ n nd, by simp [h _ nd]

lemma nnreal.summable_iff_on_nat_less {f : ℤ → ℝ≥0} (d : ℤ) (h : ∀ {n : ℤ}, n < d → f n = 0) :
  summable f ↔ summable (λ n : ℕ, f n) :=
nnreal.summable_coe.symm.trans $ (summable_iff_on_nat_less d (λ n nd,
  ((f n).coe_eq_zero.mpr (h nd)))).trans nnreal.summable_coe

lemma int.summable_iff_on_nat {f : ℤ → ℤ} {ρ : ℝ≥0} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
summable (λ n, ∥ f n ∥ * ρ ^ n) ↔ summable (λ n : ℕ, ∥ f n ∥ * ρ ^ (n : ℤ)) :=
summable_iff_on_nat_less d (λ n nd, by simp [h _ nd])

lemma summable_smaller_radius_norm {f : ℤ → ℤ} {ρ : ℝ≥0} (d : ℤ) (ρ_half : 1 / 2 < ρ)
(hf : summable (λ n : ℤ, ∥ f n ∥ * ρ ^ n))
  (hd : ∀ n : ℤ, n < d → f n = 0) : --(F : ℒ S) (s : S) :
  summable (λ n, ∥ f n ∥ * (1 / 2) ^ n) :=
begin
  refine int_summable_iff.mpr ⟨_, _⟩,
  { apply (int_summable_iff.mp hf).1.smaller_radius ρ_half.le (by simp) },
  { apply summable_of_eventually_zero (λ n, ∥f n∥ * (1 / 2) ^ n) d (λ n nd, by simp [hd _ nd]) }
end

lemma summable_smaller_radius {f : ℤ → ℤ} {ρ : ℝ≥0} (d : ℤ)
  (hf : summable (λ n : ℤ, ∥ f n ∥ * ρ ^ n)) (hd : ∀ n : ℤ, n < d → f n = 0) (hρ : (1 / 2) < ρ) :
  summable (λ n, (f n : ℝ) * (1 / 2) ^ n) :=
begin
  refine summable_of_summable_norm _,
  simp_rw [norm_mul, norm_zpow, norm_div, real.norm_two, norm_one],
  apply (summable_iff_on_nat_less d _).mpr,
  apply summable.smaller_radius _ hρ.le,
  { exact  (λ x, norm_nonneg _) },
  { simpa using (int_summable_iff.mp hf).1 },
  { exact λ n nd, by simp [hd _ nd] }
end

lemma prod_nat_summable {f : ℤ → ℤ} {r : ℝ≥0} (r_half : 1 / 2 < r)
  (hf : summable (λ n : ℤ, ∥ f n ∥ * r ^ n)) :
  summable (λ lj: ℕ × ℕ,
    (1 / 2 : ℝ) * ∥ (f (lj.fst + 1 + lj.snd) : ℝ) * (1/2)^(lj.snd) ∥ * r ^ (lj.fst)) :=
begin
  have r0 : r ≠ 0 := by { rintro rfl, simpa only [not_lt_zero'] using r_half },
  have : summable (λ (n : ℤ), ∥(f n : ℝ) * (2 * r)⁻¹∥ * r ^ n),
  { convert_to summable (λ (z : ℤ), (1 / (2 * r) : ℝ) • (∥f z∥ * ↑r ^ z)),
    { ext,
      field_simp,
      congr' 0 },
    { exact summable.const_smul hf } },
  convert prod_nat_summable_aux (_ : 1 / (2 * r) < 1) this,
  { ext,
    field_simp [r0],
    ring_exp },
  { exact nnreal.div_lt_one_of_lt ((nnreal.div_lt_iff' two_ne_zero).mp r_half) }
end

lemma fiberwise_summable_norm {f : ℤ → ℤ} {r : ℝ≥0} (d : ℤ) (r_half : 1 / 2 < r)
  (hf : summable (λ n : ℤ, ∥ f n ∥ * r ^ n))
  (hd : ∀ n : ℤ, n < d → f n = 0) :
  summable (λ (n : ℕ), 1 / 2 * ∥ ∑' (i : ℕ), (f (n + 1 + i) : ℝ) * (1 / 2) ^ i ∥ * ↑r ^ n) :=
begin
  have r_pos : ∀ (b : ℕ), 0 < (r : ℝ) ^ b :=
    pow_pos (lt_trans (by exact nnreal.coe_pos.mp (one_div_pos.mpr zero_lt_two)) r_half),
  have smaller_shift : ∀ (b : ℕ), summable (λ j : ℕ, ∥ (f (b + 1 + j) : ℝ)  * (1 / 2) ^ j ∥),
  { intro b,
    refine (summable_mul_right_iff (by norm_num : (1 / 2 : ℝ) ^ (b + 1) ≠ 0)).mpr _,
    obtain hff := (equiv.add_group_add (b+1 : ℤ)).summable_iff.mpr (summable_smaller_radius_norm d
      r_half hf hd),
    convert (summable_iff_on_nat_less (d - (b + 1)) _).mp hff,
    { ext,
      simp [mul_assoc, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0) (b+1), mul_inv₀, zpow_coe_nat,
        mul_comm ((2 : ℝ) ^ x)⁻¹], refl },
    { exact λ n nd, by simp [hd _ (lt_sub_iff_add_lt'.mp nd)] } },
  set ϕ := λ lj: ℕ × ℕ,
    (1 / 2 : ℝ) * ∥ (f (lj.fst + 1 + lj.snd) : ℝ) * (1/2)^(lj.snd) ∥ * r ^ (lj.fst),
  have H : ∀ b : ℕ, summable (λ i : ℕ, ϕ(b, i)) :=
    λ n, (summable_mul_right_iff (r_pos n).ne').mp ((smaller_shift n).mul_left (1 / 2)),
  have := (has_sum.prod_fiberwise (prod_nat_summable r_half hf).has_sum
    (λ b, (H b).has_sum)).summable,
  dsimp [ϕ] at this,
  apply summable_of_nonneg_of_le (λ b, _) (λ b, _) this,
  { exact mul_nonneg (mul_nonneg one_half_pos.le (norm_nonneg _)) (r_pos b).le },
  { simp_rw mul_assoc,
    rw [tsum_mul_left, mul_le_mul_left (@one_half_pos ℝ _), tsum_mul_right,
      mul_le_mul_right (r_pos b)],
    exact norm_tsum_le_tsum_norm (smaller_shift b) }
end

lemma summable_convolution {r : ℝ≥0} (r_half : 1 / 2 < r) (f : ℤ → ℤ) (d : ℤ)
  (hf : summable (λ n, ∥ f n ∥ * r ^ n)) (hd : ∀ n : ℤ, n < d → f n = 0)
  (hd_shift : ∀ (n : ℤ), n < d → ∥∑' (i : ℕ), (f (n + 1 + i) : ℝ) * (1 / 2) ^ i∥ = 0) :
  summable (λ n : ℤ, (1 / 2) * ∥ tsum (λ i : ℕ, ((f (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ n) :=
begin
  suffices h_on_nat : summable (λ (n : ℕ),
    (1 / 2) * ∥∑' (i : ℕ), (f (n + 1 + i) : ℝ) * (1 / 2) ^ i∥ * (r : ℝ) ^ n),
  { simp_rw mul_assoc at ⊢ h_on_nat,
    rw [← summable_mul_left_iff (ne_of_gt (@one_half_pos ℝ _))] at ⊢ h_on_nat,
    refine (summable_iff_on_nat_less d (λ n hn, _)).mpr _,
    { rw [hd_shift _ hn, zero_mul] },
    { exact_mod_cast h_on_nat } },
  apply fiberwise_summable_norm d r_half hf hd,
end

end summability

end aux_thm69
