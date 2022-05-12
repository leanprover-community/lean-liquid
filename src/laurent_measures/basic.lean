import analysis.special_functions.pow
import analysis.special_functions.log.basic
import analysis.specific_limits.basic
import category_theory.Fintype
import analysis.normed_space.basic

import laurent_measures.bounded
import pseudo_normed_group.basic
import pseudo_normed_group.category

universe u

noncomputable theory
open_locale big_operators nnreal classical

/-
structure c_measures (r : ℝ≥0) (c : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable   : ∀ s, summable (λ n, (∥ to_fun s n ∥₊ * r ^ n)))
(bdd        : ∀ s, tsum (λ n, (∥ to_fun s n ∥₊ * r ^ n)) ≤ c)
-/

/-- A term of type `laurent_measures r S` is, for each `s : S`, a function `φ : ℤ → ℤ`
  (typically thought of as a power series `∑ φ(n)Tⁿ`) such that `∑ |φ(n)|rⁿ` converges.
  Note that if `0<r<1` then the support of φ can only contain finitely many negative integers.  -/
structure laurent_measures (r : ℝ≥0) (S : Fintype) :=
(to_fun    : S → ℤ → ℤ)
(summable' : ∀ s, summable (λ n, ∥to_fun s n∥₊ * r ^ n))

variables {r : ℝ≥0} {S S' : Fintype.{u}}

local notation `ℒ` := laurent_measures r

namespace laurent_measures

instance : has_coe_to_fun (ℒ S) (λ F, S → ℤ → ℤ) :=
⟨λ F, F.to_fun⟩

@[simp] lemma coe_mk (f : S → ℤ → ℤ) (hf) (s : S) (n : ℤ) :
  (@laurent_measures.mk r S f hf) s n = f s n := rfl

@[ext]
lemma ext (F G : ℒ S) : (F : S → ℤ → ℤ) = G → F = G :=
by { intros h, cases F, cases G, simpa }

lemma ext_iff (F G : ℒ S) : F = G ↔ ∀ s n, F s n = G s n :=
⟨λ h, by intros; rw h, λ h, laurent_measures.ext F G $ by ext; apply h⟩

protected lemma nnreal_summable (F : ℒ S) (s : S) : summable (λ n, ∥F s n∥₊ * r ^ n) :=
F.2 _

protected lemma summable (F : ℒ S) (s : S) : summable (λ n, ∥F s n∥ * r ^ n) :=
begin
  simpa only [← nnreal.summable_coe, nnreal.coe_mul, coe_nnnorm, nnreal.coe_zpow]
    using F.nnreal_summable s
end

-- Move me
lemma nonneg_of_norm_mul_zpow (k n : ℤ) (r : ℝ≥0) : 0 ≤ ∥ k ∥ * (r : ℝ)^n :=
mul_nonneg (norm_nonneg _) (zpow_nonneg (nnreal.coe_nonneg _) _)

def map (f : S ⟶ S') : ℒ S → ℒ S' := λ F,
{ to_fun := λ s' k, ∑ s in finset.univ.filter (λ t, f t = s'), F s k,
  summable' := begin
    intros s',
    have : ∀ n : ℤ, ∥∑ s in finset.univ.filter (λ t, f t = s'), F s n∥₊ * r^n ≤
      ∑ s in finset.univ.filter (λ t, f t = s'), ∥F s n∥₊ * r^n := λ n,
    calc ∥∑ s in finset.univ.filter (λ t, f t = s'), F s n∥₊ * r^n ≤
      (∑ s in finset.univ.filter (λ t, f t = s'), ∥F s n∥₊) * r^n :
        mul_le_mul' (nnnorm_sum_le _ _) le_rfl
      ... = _ : by rw finset.sum_mul,
    exact nnreal.summable_of_le this (summable_sum $ λ (s : S) _, F.nnreal_summable s),
  end }

@[simp] lemma map_apply (f : S ⟶ S') (F : ℒ S) (s' : S') (k : ℤ) :
  map f F s' k = ∑ s in finset.univ.filter (λ t, f t = s'), F s k := rfl

@[simp] lemma map_id : (map (𝟙 S) : ℒ S → ℒ S) = id :=
begin
  ext F s k,
  simp only [map_apply, Fintype.id_apply, id.def, finset.sum_filter,
    finset.sum_ite_eq', finset.mem_univ, if_true],
end

@[simp] lemma map_comp {S'' : Fintype.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
  (map (f ≫ g) : ℒ S → ℒ S'') = map g ∘ map f :=
begin
  ext F s k,
  simp only [function.comp_app, map_apply, finset.sum_congr],
  rw ← finset.sum_bUnion,
  { apply finset.sum_congr,
    { change finset.univ.filter (λ t, g (f t) = s) = _,
      ext i,
      split;
      { intro hi, simpa only [finset.mem_bUnion, finset.mem_filter, finset.mem_univ, true_and,
          exists_prop, exists_eq_right'] using hi } },
    { intros, refl } },
  { intros i hi j hj h k hk,
    simp only [finset.inf_eq_inter, finset.mem_inter, finset.mem_filter, finset.mem_univ, true_and,
      finset.coe_filter, finset.coe_univ, set.sep_univ, set.mem_set_of_eq] at hi hj hk,
    refine h _,
    rw [← hk.1, ← hk.2] }
end

def add : ℒ S → ℒ S → ℒ S := λ F G,
{ to_fun := F + G,
  summable' := λ s, begin
    refine nnreal.summable_of_le _ ((F.nnreal_summable s).add (G.nnreal_summable s)),
    intros n,
    rw ← add_mul,
    exact mul_le_mul' (nnnorm_add_le _ _) le_rfl,
  end }

instance : has_add (ℒ S) := ⟨add⟩

@[simp]
lemma add_apply (F G : ℒ S) (s : S) (n : ℤ) : (F + G) s n = F s n + G s n := rfl

def zero : ℒ S :=
{ to_fun := 0,
  summable' := λ s, by simp [summable_zero] }

instance : has_zero (ℒ S) := ⟨zero⟩

@[simp] lemma zero_apply (s : S) (n : ℤ) : (0 : ℒ S) s n = 0 := rfl

def neg : ℒ S → ℒ S := λ F,
{ to_fun := - F,
  summable' := λ s, by simp [F.nnreal_summable] }

instance : has_neg (ℒ S) := ⟨neg⟩

@[simp] lemma neg_apply (F : ℒ S) (s : S) (n : ℤ) : (-F) s n = - (F s n) := rfl

def sub : ℒ S → ℒ S → ℒ S := λ F G,
{ to_fun := F - G,
  summable' := (add F (neg G)).nnreal_summable }

instance : has_sub (ℒ S) := ⟨sub⟩

@[simp] lemma sub_apply (F G : ℒ S) (s : S) (n : ℤ) : (F - G) s n = F s n - G s n := rfl

example (a m : ℤ) : (-a)*m=a*(-m) := neg_mul_comm a m

-- move me
instance : has_continuous_smul ℕ ℝ≥0 :=
{ continuous_smul := begin
    let f : ℕ × ℝ≥0 → ℝ≥0 × ℝ≥0 := prod.map coe id,
    have hf : continuous f := continuous.prod_map continuous_bot continuous_id,
    simpa only [nsmul_eq_mul] using continuous_mul.comp hf,
end }

-- move me
@[simp] lemma _root_.int.norm_mul (m n : ℤ) : ∥m * n∥ = ∥m∥ * ∥n∥ :=
by simp only [int.norm_eq_abs, int.cast_mul, abs_mul]

-- move me
@[simp] lemma _root_.int.nnnorm_mul (m n : ℤ) : ∥m * n∥₊ = ∥m∥₊ * ∥n∥₊ :=
by ext; simp only [coe_nnnorm, int.norm_mul, nonneg.coe_mul]

-- move me
@[simp] lemma _root_.nat.norm_coe_int (n : ℕ) : ∥(n : ℤ)∥ = n :=
by simp only [int.norm_eq_abs, int.cast_coe_nat, nat.abs_cast]

-- move me
@[simp] lemma _root_.nat.nnnorm_coe_int (n : ℕ) : ∥(n : ℤ)∥₊ = n :=
by ext; simp only [coe_nnnorm, nat.norm_coe_int, nnreal.coe_nat_cast]

instance : add_comm_monoid (ℒ S) :=
{ add_assoc := λ a b c, by { ext, simp only [add_assoc, add_apply] },
  add_comm := λ F G, by { ext, simp only [add_comm, add_apply] },
  zero_add := λ a, by { ext, simp only [zero_add, add_apply, zero_apply] },
  add_zero := λ a, by { ext, simp only [add_zero, add_apply, zero_apply] },
  nsmul := λ n F,
  { to_fun := λ s k, n • (F s k),
    summable' := λ s, begin
      -- aahrg, why is `n` an implicit variable here???
      have := @summable.const_smul _ _ _ _ _ _ _ _ _ n (F.nnreal_summable s),
      simpa only [nsmul_eq_mul, int.nat_cast_eq_coe_nat, int.nnnorm_mul,
        nat.nnnorm_coe_int, mul_assoc],
    end },
  nsmul_zero' := λ F, by { ext, refl },
  nsmul_succ' := λ n F, by { ext, refl },
  ..(infer_instance : has_add _),
  ..(infer_instance : has_zero _) }

instance : add_comm_group (ℒ S) :=
{ neg := neg,
  sub := sub,
  sub_eq_add_neg := λ F G, by { ext, refl },
  zsmul := λ n F,
  { to_fun := λ s m, n • (F s m),
    summable' := λ s, begin
      -- aahrg, why is `n.nat_abs` an implicit variable here???
      have := @summable.const_smul _ _ _ _ _ _ _ _ _ n.nat_abs (F.nnreal_summable s),
      simpa only [nsmul_eq_mul, nnreal.coe_nat_abs, algebra.id.smul_eq_mul,
        int.nnnorm_mul, mul_assoc],
    end },
  zsmul_zero' := λ F, by { ext, simp only [algebra.id.smul_eq_mul, zero_mul, coe_mk, zero_apply], },
  zsmul_succ' := λ n F, by { ext, simp only [add_apply, int.coe_nat_succ, int.of_nat_eq_coe,
    zsmul_eq_smul, smul_eq_mul, add_mul, add_comm, one_mul, coe_mk], },
  zsmul_neg' := λ n F, by { ext, rw neg_apply, simp only [neg_apply, int.coe_nat_succ, int.of_nat_eq_coe,
    int.neg_succ_of_nat_coe, add_comm, zsmul_eq_smul, smul_eq_mul], dsimp, ring_nf},
  add_left_neg := λ F, by { ext, simp only [zero_apply, add_apply, neg_apply, add_left_neg], },
  add_comm := λ a b, by { ext, dsimp, rw add_comm },
  ..(infer_instance : add_comm_monoid _),
  ..(infer_instance : has_neg _),
  ..(infer_instance : has_sub _) }.

instance : has_norm (ℒ S) :=
⟨λ F, ∑ s, ∑' n, ∥F s n∥ * (r : ℝ) ^ n⟩

lemma norm_def (F : ℒ S) : ∥F∥ = ∑ s, ∑' n, ∥F s n∥ * (r : ℝ)^n := rfl

instance : has_nnnorm (ℒ S) :=
⟨λ F, ∑ s, ∑' n, ∥F s n∥₊ * r ^ n⟩

lemma nnnorm_def (F : ℒ S) : ∥F∥₊ = ∑ s, ∑' n, ∥F s n∥₊ * r^n := rfl

@[simp] lemma coe_nnnorm (F : ℒ S) : (∥F∥₊ : ℝ) = ∥F∥ :=
by simp only [nnnorm_def, norm_def, nnreal.coe_sum, nnreal.coe_tsum,
  nonneg.coe_mul, coe_nnnorm, nnreal.coe_zpow]

@[simp] lemma laurent_measures.norm_nonneg (F : ℒ S) : 0 ≤ ∥F∥ :=
by rw [← coe_nnnorm]; exact ∥F∥₊.coe_nonneg

@[simp] lemma nnnorm_neg (F : ℒ S) : ∥-F∥₊ = ∥F∥₊ :=
by simp only [nnnorm_def, neg_apply, nnnorm_neg]

lemma nnnorm_add (F G : ℒ S) : ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  simp only [nnnorm_def, ← finset.sum_add_distrib],
  apply finset.sum_le_sum,
  rintro s -,
  rw ← tsum_add (F.nnreal_summable _) (G.nnreal_summable _),
  refine tsum_le_tsum _ ((F + G).nnreal_summable _)
    ((F.nnreal_summable s).add (G.nnreal_summable s)),
  intro b,
  simp [← add_mul],
  refine mul_le_mul' (nnnorm_add_le _ _) le_rfl
end

lemma norm_add (F G : ℒ S) : ∥F + G∥ ≤ ∥F∥ + ∥G∥ :=
by simpa only [← coe_nnnorm, ← nnreal.coe_add, nnreal.coe_le_coe] using nnnorm_add F G

@[simp] lemma nsmul_apply (k : ℕ) (F : ℒ S) (s : S) (n : ℤ) : (k • F) s n = k • (F s n) := rfl

@[simp] lemma zsmul_apply (k : ℤ) (F : ℒ S) (s : S) (n : ℤ) : (k • F) s n = k • (F s n) := rfl

section
open finset

lemma map_bound (f : S ⟶ S') (F : ℒ S) : ∥map f F∥₊ ≤ ∥F∥₊ := calc
∥map f F∥₊ = ∑ s', ∑' n, ∥∑ s in univ.filter (λ t, f t = s'), F s n∥₊ * _ : rfl
... ≤ ∑ s', ∑' n, ∑ s in univ.filter (λ t, f t = s'), ∥F s n∥₊ * r^n : begin
  apply sum_le_sum,
  rintros s' -,
  have h1 : summable (λ n : ℤ, ∑ (s : S.α) in univ.filter (λ t, f t = s'), ∥F s n∥₊ * r^n) :=
    summable_sum (λ s _, F.nnreal_summable s),
  have h2 : ∀ b : ℤ,
    ∥∑ (s : S.α) in univ.filter (λ t, f t = s'), F s b∥₊ * r ^ b ≤
      ∑ (s : S.α) in univ.filter (λ t, f t = s'), ∥F s b∥₊ * r ^ b,
  { intros b, rw ← sum_mul, exact mul_le_mul' (nnnorm_sum_le _ _) le_rfl },
  apply tsum_le_tsum h2 (nnreal.summable_of_le h2 h1) h1,
end
... = ∑ s', ∑ s in univ.filter (λ t, f t = s'), ∑' n, ∥F s n∥₊ * r^n :
  sum_congr rfl (λ s' _, tsum_sum $ λ s _, F.nnreal_summable _)
... = _ : begin
  rw [← sum_bUnion],
  refine sum_congr _ _,
  { ext s, simp only [mem_bUnion, mem_univ, mem_filter, true_and, exists_true_left, exists_eq'] },
  { intros, refl },
  { rintro x - y - h i hi,
    apply h,
    simp only [inf_eq_inter, mem_inter, mem_filter, mem_univ, true_and] at hi,
    rw [← hi.1, ← hi.2] }
end

end

lemma map_bound' (f : S ⟶ S') (F : ℒ S) : ∥map f F∥ ≤ ∥F∥ :=
by simpa only [← coe_nnnorm, ← nnreal.coe_add, nnreal.coe_le_coe] using map_bound f F


/-
lemma exists_c (F : ℒ S) : ∃ (c : ℝ≥0),
  ∀ s : S, ∑' n, ∥ F s n ∥ * r ^ n ≤ c :=
begin
  use ∑ s, ∑' n, ∥ F s n ∥ * r ^ n,
  { apply finset.sum_nonneg,
    rintros s -,
    apply tsum_nonneg,
    intros n,
    refine mul_nonneg (norm_nonneg _) (zpow_nonneg _ _),
    exact nnreal.coe_nonneg r, },
  { admit },
end
-/

/-- This lemma puts bounds on where `F s n` can be nonzero. -/
lemma eq_zero_of_filtration (F : ℒ S) (c : ℝ≥0) :
  ∥F∥₊ ≤ c → ∀ (s : S) (n : ℤ), c < r^n → F s n = 0 :=
begin
  intros hF s n h,
  suffices : ∥F s n∥₊ < 1,
  { change abs (F s n : ℝ) < 1 at this,
    norm_cast at this,
    rwa ← int.abs_lt_one_iff },
  have : ∥F s n∥₊ * r ^ n ≤ ∑' k, ∥F s k∥₊ * r ^ k,
  { exact le_tsum (F.nnreal_summable s) _ (λ k _, zero_le'), },
  replace this := lt_of_le_of_lt (this.trans _) h,
  { have hr₁ : 0 < r^n := lt_of_le_of_lt zero_le' h,
    have hr₂ : r^n ≠ 0 := hr₁.ne',
    convert mul_lt_mul this (le_refl (r ^ n)⁻¹) _ hr₁.le,
    { exact (mul_inv_cancel_right₀ hr₂ _).symm },
    { exact (mul_inv_cancel hr₂).symm },
    { rwa nnreal.inv_pos }, },
  { refine le_trans _ hF,
    apply @finset.single_le_sum S ℝ≥0 _ (λ s, ∑' n, ∥F s n∥₊ * r^n),
    { rintros s -, exact zero_le', },
    { exact finset.mem_univ _ } }
end

-- move me
lemma zpow_strict_anti {K : Type} [linear_ordered_field K] {x : K} (hx₀ : 0 < x) (hx₁ : x < 1) :
  strict_anti (λ n:ℤ, x ^ n) :=
begin
  intros n m H,
  rw [← inv_inv x],
  simp only [inv_zpow₀ x⁻¹, inv_lt_inv (zpow_pos_of_pos (inv_pos.mpr hx₀) _)
    (zpow_pos_of_pos (inv_pos.mpr hx₀) _)],
  exact zpow_strict_mono (one_lt_inv hx₀ hx₁) H,
end

open real

--For every F, d F is a bound whose existence is established in `eq_zero_of_filtration`
lemma exists_bdd_filtration {S : Fintype} (hr₀ : 0 < (r : ℝ)) (hr₁ : (r : ℝ) < 1) (F : ℒ S) :
  ∃ d : ℤ, ∀ s : S, ∀ (n : ℤ), n < d → F s n = 0 :=
begin
  have h_logr : (log r) < 0 := log_neg hr₀ hr₁,
  let d := if log ∥ F ∥ ≥ 0 then ⌊ (log ∥ F ∥ / log (r : ℝ)) ⌋ - 1 else -1,
  use d,
  intros s n hn,
  have H1 := zpow_strict_anti hr₀ hr₁ hn,
  suffices H2 : ∥F∥₊ < r ^ d,
  { refine eq_zero_of_filtration F (∥F∥₊) le_rfl s n (H2.trans _),
    rw [← nnreal.coe_lt_coe, nnreal.coe_zpow, nnreal.coe_zpow],
    exact zpow_strict_anti hr₀ hr₁ hn, },
  have hd1 : 0 < -(d : ℝ),
  { rw [lt_neg, neg_zero, ← int.cast_zero, int.cast_lt],
    apply int.lt_of_le_sub_one,
    dsimp only [d],
    split_ifs,
    { rw [tsub_le_iff_right, sub_add, sub_self, sub_zero],
      exact int.floor_nonpos (div_nonpos_of_nonneg_of_nonpos h(le_of_lt h_logr)) },
    { simp only [zero_sub] } },
  have hFd1 : (log ∥ F ∥) < d * (log (r : ℝ)),
  { rw ← zsmul_eq_mul,
    rw ite_smul,
    split_ifs,
    { rw zsmul_eq_mul,
      calc (log ∥F∥)
          = (log ∥F∥/log r) * log r : (div_mul_cancel (log ∥F∥) (ne_of_lt h_logr)).symm
      ... ≤ ⌊ (log ∥F∥)/log r⌋ * log r : (mul_le_mul_right_of_neg h_logr).mpr (int.floor_le _)
      ... < (⌊ (log ∥F∥)/log r⌋ - 1) * log r : (mul_lt_mul_right_of_neg h_logr).mpr (sub_one_lt _)
      ... = ↑(⌊ (log ∥F∥)/log r⌋ - 1) * log r : by simp only [int.cast_one, int.cast_sub] },
    { rw [neg_smul, one_smul],
      rw [ge_iff_le, not_le] at h,
      apply h.trans,
      rwa [lt_neg, neg_zero] } },
  rw [← nnreal.coe_lt_coe, nnreal.coe_zpow, coe_nnnorm],
  have := (real.lt_rpow_of_log_lt (laurent_measures.norm_nonneg F) hr₀ hFd1),
  rwa [real.rpow_int_cast _ d] at this,
end

def bdd_filtration {S : Fintype} (hr₀ : 0 < (r : ℝ)) (hr₁ : (r : ℝ) < 1) (F : ℒ S) : ℤ :=
(exists_bdd_filtration hr₀ hr₁ F).some

def bdd_filtration_spec {S : Fintype} (hr₀ : 0 < (r : ℝ)) (hr₁ : (r : ℝ) < 1) (F : ℒ S) :
∀ s n, n < bdd_filtration hr₀ hr₁ F → F s n = 0 := (exists_bdd_filtration hr₀ hr₁ F).some_spec

section profinite_structure

@[simps] def truncate {c : ℝ≥0} (A : finset ℤ) :
  { F : ℒ S | ∥F∥₊ ≤ c } → laurent_measures_bdd r S A c := λ F,
{ to_fun := λ s i, F s i,
  bound' := begin
    refine (finset.sum_le_sum $ λ s _, _).trans F.2,
    convert sum_le_tsum A _ ((F : ℒ S).nnreal_summable s) using 1,
    { conv_rhs { rw ← finset.sum_attach }, refl },
    { intros b hb, exact zero_le', },
  end }

lemma eq_iff_truncate_eq (c : ℝ≥0) (F G : {F : ℒ S | ∥F∥₊ ≤ c}) :
  (∀ k, truncate k F = truncate k G) → F = G :=
begin
  intros h,
  ext s i,
  specialize h {i},
  apply_fun (λ e, e s ⟨i, by simp⟩) at h,
  exact h,
end


def finset_map {A B : finset ℤ} (h : B ≤ A) : B → A :=
λ i, ⟨i, h i.2⟩

def transition {c : ℝ≥0} {A B : finset ℤ} (h : B ≤ A) :
  laurent_measures_bdd r S A c → laurent_measures_bdd r S B c := λ F,
⟨λ s i, F s (finset_map h i), begin
  refine (finset.sum_le_sum $ λ s _, _).trans F.2,
  have : ∑ i : B, ∥F s (finset_map h i)∥₊ * r^(i : ℤ) =
    ∑ i in finset.univ.image (finset_map h), ∥F s i∥₊ * r^(i : ℤ),
  { rw finset.sum_image,
    { refl },
    { rintros i - j - hh,
      apply subtype.ext,
      apply_fun (λ e, e.val) at hh,
      exact hh } },
  rw this,
  refine finset.sum_le_sum_of_subset_of_nonneg (finset.subset_univ _) (λ _ _ _, zero_le'),
end⟩

def mk_seq {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c) :
  S → ℤ → ℤ := λ s i, F {i} s ⟨i, by simp⟩

lemma mk_seq_compat {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c)
  (compat : ∀ (A B : finset ℤ) (h : B ≤ A), transition h (F _) = F _) (s : S)
  (A : finset ℤ) (i : A) : mk_seq F s i = F A s i :=
begin
  have : ({i} : finset ℤ) ≤ A, { simp },
  specialize compat _ _ this,
  dsimp [mk_seq],
  rw ← compat,
  change (F A) s _ = _,
  congr,
  ext,
  refl,
end

lemma mk_seq_compat_summable {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c)
  (compat : ∀ (A B : finset ℤ) (h : B ≤ A), transition h (F _) = F _) (s : S) :
  summable (λ k : ℤ, ∥mk_seq F s k∥ * (r:ℝ)^k) :=
begin
  apply summable_of_sum_le,
  { intro k,
    dsimp,
    refine mul_nonneg (norm_nonneg _) (zpow_nonneg (nnreal.coe_nonneg _) _) },
  { intros A,
    rw ← finset.sum_attach,
    refine le_trans _ (F A).bound,
    simp_rw mk_seq_compat _ compat,
    simp only [laurent_measures_bdd.nnnorm_def, finset.univ_eq_attach, nnreal.coe_sum,
      nnreal.coe_mul, nnreal.coe_zpow],
    apply @finset.single_le_sum S ℝ _ (λ s, ∑ (i : A), ∥ F A s i ∥ * (r : ℝ)^(i : ℤ)),
    swap, { simp },
    rintro s -,
    apply finset.sum_nonneg,
    rintros a -,
    refine mul_nonneg (norm_nonneg _) (zpow_nonneg (nnreal.coe_nonneg _) _) },
end

lemma mk_seq_compat_nnreal_summable {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c)
  (compat : ∀ (A B : finset ℤ) (h : B ≤ A), transition h (F _) = F _) (s : S) :
  summable (λ k : ℤ, ∥mk_seq F s k∥₊ * r^k) :=
begin
  rw ← nnreal.summable_coe,
  simpa only [nonneg.coe_mul, coe_nnnorm, nnreal.coe_zpow] using mk_seq_compat_summable F compat s
end

lemma mk_seq_compat_sum_le {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c)
  (compat : ∀ (A B : finset ℤ) (h : B ≤ A), transition h (F _) = F _)  :
  ∑ (s : S), ∑' (k : ℤ), ∥mk_seq F s k∥₊ * r^k ≤ c :=
begin
  rw ← tsum_sum,
  swap, { intros s hs, apply mk_seq_compat_nnreal_summable _ compat },
  have : ∀ A : finset ℤ,
    ∑ (b : A), ∑ (s : S), ∥F A s b∥₊ * r^(b : ℤ) ≤ c,
  { intros A,
    rw finset.sum_comm,
    exact (F A).bound },
  apply tsum_le_of_sum_le,
  { apply summable_sum,
    intros s hs,
    apply mk_seq_compat_nnreal_summable _ compat },
  intros I,
  rw finset.sum_comm,
  convert (F I).bound using 1,
  dsimp,
  apply finset.sum_congr rfl,
  rintros s -,
  rw ← finset.sum_attach,
  apply finset.sum_congr rfl,
  rintros i -,
  simp_rw [mk_seq_compat _ compat],
end

lemma exists_of_compat {c} (F : Π (A : finset ℤ), laurent_measures_bdd r S A c)
  (compat : ∀ (A B : finset ℤ) (h : B ≤ A),
    transition h (F _) = F _) :
  ∃ (G : {H : ℒ S | ∥H∥₊ ≤ c }), ∀ (k : finset ℤ), truncate k G = F k :=
begin
  let G : ℒ S := ⟨mk_seq F, mk_seq_compat_nnreal_summable _ compat⟩,
  use G,
  { apply mk_seq_compat_sum_le _ compat },
  { intros k,
    ext s i,
    change F _ _ _ = _,
    have := compat k {i} (by simp),
    apply_fun (λ e, e s ⟨i, by simp⟩) at this,
    erw ← this,
    change F k _ _ = F k _ _,
    congr,
    ext, refl }
end

variables (r S)
open category_theory
/-- `laurent_measures_bdd_functor r S c` is the contravariant functor sending `T : finset ℤ` to
  the finite type `laurent_measures_bdd r S T c`. Morphisms are given by throwing away
  coefficients. -/
def laurent_measures_bdd_functor (c : ℝ≥0) [fact (0 < r)] :
  (as_small (finset ℤ))ᵒᵖ ⥤ Fintype :=
{ obj := λ A, Fintype.of $ laurent_measures_bdd r S (ulift.down A.unop) c,
  map := λ A B f, transition (le_of_hom $ ulift.down f.unop) }.

/-- The `equiv` between Laurent measures with norm at most `c` and the projective limit
over `T : finset ℤ` of the finite types `laurent_measures_bdd r S T c`. -/
def laurent_measures_bdd_equiv (c : ℝ≥0) [fact (0 < r)] : { F : ℒ S | ∥F∥₊ ≤ c } ≃
  (Profinite.limit_cone (laurent_measures_bdd_functor r S c ⋙ Fintype.to_Profinite)).X :=
equiv.of_bijective (λ F, ⟨λ A, truncate (ulift.down A.unop) F, λ A B f, by { ext, refl }⟩)
begin
  split,
  { intros F G h,
    apply eq_iff_truncate_eq,
    intros k,
    dsimp at h,
    apply_fun (λ e, e.1 (opposite.op ⟨k⟩)) at h,
    exact h },
  { rintros ⟨F, hF⟩,
    dsimp at F hF,
    obtain ⟨G,hG⟩ := exists_of_compat (λ A, F (opposite.op ⟨A⟩)) _,
    { use G,
      ext : 2,
      dsimp,
      have := hG (ulift.down x.unop),
      convert this,
      rw ← x.op_unop,
      congr' 1,
      ext,
      refl },
    { intros A B h,
      let e : (opposite.op $ as_small.up.obj A) ⟶ (opposite.op $ as_small.up.obj B) :=
        quiver.hom.op (as_small.up.map (hom_of_le h)),
      exact hF e } }
end

/-- The profinite topology on the Laurent measures with norm at most `c`. -/
instance (c : ℝ≥0) [fact (0 < r)] : topological_space {F : ℒ S | ∥F∥₊ ≤ c} :=
topological_space.induced (laurent_measures_bdd_equiv r S c) infer_instance

def laurent_measures_bdd_homeo (c : ℝ≥0) [fact (0 < r)] : { F : ℒ S | ∥F∥₊ ≤ c } ≃ₜ
  (Profinite.limit_cone (laurent_measures_bdd_functor r S c ⋙ Fintype.to_Profinite)).X :=
{ continuous_to_fun := continuous_induced_dom,
  continuous_inv_fun := begin
    have : inducing (laurent_measures_bdd_equiv r S c) := ⟨rfl⟩,
    rw this.continuous_iff,
    dsimp,
    simp only [equiv.self_comp_symm],
    exact continuous_id,
  end,
  ..(laurent_measures_bdd_equiv _ _ _) }

instance (c : ℝ≥0) [fact (0 < r)] : t2_space { F : ℒ S | ∥F∥₊ ≤ c } :=
(laurent_measures_bdd_homeo r S c).symm.t2_space

instance (c : ℝ≥0) [fact (0 < r)] : totally_disconnected_space { F : ℒ S | ∥F∥₊ ≤ c } :=
(laurent_measures_bdd_homeo r S c).symm.totally_disconnected_space

instance (c : ℝ≥0) [fact (0 < r)] : compact_space {F : ℒ S | ∥F∥₊ ≤ c} :=
(laurent_measures_bdd_homeo r S c).symm.compact_space

@[continuity]
lemma truncate_continuous (c : ℝ≥0) [fact (0 < r)] (A : finset ℤ) :
  continuous (truncate A : _ → laurent_measures_bdd r S _ c) :=
begin
  let g₁ :=
    (Profinite.limit_cone (laurent_measures_bdd_functor.{u} r S c ⋙ Fintype.to_Profinite)).π.app
    (opposite.op $ ulift.up A),
  let g₂ := (laurent_measures_bdd_homeo r S c),
  change continuous (g₁ ∘ g₂),
  continuity,
end

lemma continuous_iff (c : ℝ≥0) [fact (0 < r)] {α : Type*} [topological_space α]
  (f : α → { F : ℒ S | ∥F∥₊ ≤ c }) :
  continuous f ↔ ∀ (A : finset ℤ), continuous ((truncate A) ∘ f) :=
begin
  split,
  { intros hf A, continuity },
  { intros h,
    rw ← (laurent_measures_bdd_homeo r S c).comp_continuous_iff,
    apply continuous_subtype_mk,
    apply continuous_pi,
    intros A,
    apply h }
end

end profinite_structure

/-
--should this be a coercion?
def c_measures_to_oc (r : ℝ≥0) (c : ℝ≥0) (S : Type*) (hS : fintype S) :
  c_measures r c S hS → ℒ S hS := λ f, ⟨f.to_fun, f.summable⟩

lemma laurent_measures_are_c (r : ℝ≥0) (S : Type*) (hS : fintype S) (F : ℒ S hS) :
  ∃ (c : ℝ≥0) (f : c_measures r c S hS),
  c_measures_to_oc r c S hS f = F := by admit
-/

--needed?
instance : pseudo_normed_group (ℒ S) :=
{ filtration := λ c, { F | ∥F∥₊ ≤ c },
  filtration_mono := λ c₁ c₂ h F hF, by {dsimp at *, exact le_trans hF h},
  zero_mem_filtration := λ c, by simp [nnnorm_def],
  neg_mem_filtration := λ c F h, (nnnorm_neg F).le.trans h,
  add_mem_filtration := λ c₁ c₂ F₁ F₂ h₁ h₂, (nnnorm_add _ _).trans (add_le_add h₁ h₂) }

@[simp] lemma mem_filtration_iff (F : ℒ S) (c : ℝ≥0) :
  F ∈ pseudo_normed_group.filtration (ℒ S) c ↔ ∥F∥₊ ≤ c := iff.rfl

instance [fact (0 < r)] : profinitely_filtered_pseudo_normed_group (ℒ S) :=
{ continuous_add' := begin
    intros c₁ c₂,
    rw continuous_iff,
    intros A,
    let E : laurent_measures_bdd r S A c₁ × laurent_measures_bdd r S A c₂ →
      laurent_measures_bdd r S A (c₁ + c₂) := λ G, ⟨G.1 + G.2, _⟩,
    swap, {
      refine le_trans _ (add_le_add G.fst.2 G.snd.2),
      rw ← finset.sum_add_distrib,
      apply finset.sum_le_sum,
      intros i hi,
      rw ← finset.sum_add_distrib,
      apply finset.sum_le_sum,
      intros j hj,
      rw ← add_mul,
      refine mul_le_mul' (norm_add_le _ _) le_rfl, },
    have :
      (truncate A : _ → laurent_measures_bdd r S A (c₁ + c₂)) ∘ pseudo_normed_group.add' =
      E ∘ (prod.map (truncate A) (truncate A)),
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply continuous.prod_map,
      all_goals {apply truncate_continuous} }
  end,
  continuous_neg' := begin
    intros c,
    rw continuous_iff,
    intros A,
    let E : laurent_measures_bdd r S A c → laurent_measures_bdd r S A c :=
      λ G, ⟨- G, _⟩,
    swap, {
      convert G.2 using 1,
      apply finset.sum_congr rfl,
      intros s hs,
      apply finset.sum_congr rfl,
      intros x hx,
      congr' 1,
      simpa },
    have : (truncate A : _ → laurent_measures_bdd r S A c) ∘ pseudo_normed_group.neg' =
      E ∘ truncate A,
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply truncate_continuous }
  end,
  continuous_cast_le := begin
    introsI c₁ c₂ h,
    rw continuous_iff,
    intros A,
    let g : laurent_measures_bdd r S A c₁ → laurent_measures_bdd r S A c₂ :=
      λ g, ⟨g, le_trans g.2 h.out⟩,
    have : (truncate A : _ → laurent_measures_bdd r S A c₂) ∘ pseudo_normed_group.cast_le =
      g ∘ truncate A,
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply truncate_continuous }
  end,
  ..(infer_instance : (pseudo_normed_group (ℒ S))) }
.

/-- The additive group homomorphism on Laurent measures induced by division by `T^k` on `ℤ((T))ᵣ` -/
@[simps] def shift_add_monoid_hom [hr : fact (0 < r)] (k : ℤ) : ℒ S →+ ℒ S :=
add_monoid_hom.mk' (λ F,
{ to_fun := λ s n, F s (n+k),
  summable' := λ s, begin
    convert (nnreal.summable_comp_injective
      (F.nnreal_summable s) (add_left_injective (k:ℤ))).mul_right (r ^ -k),
    ext n,
    simp only [function.comp, ← zpow_add₀ hr.out.ne', mul_assoc, add_neg_cancel_right],
  end })
(λ F G, by { ext, refl })
.

-- move me
@[simp, to_additive] lemma _root_.finset.prod_attach' {α M : Type*} [comm_monoid M]
  (s : finset α) (f : s → M) :
  ∏ a in s.attach, f a = ∏ a in s, if h : a ∈ s then f ⟨a, h⟩ else 1 :=
begin
  rw [eq_comm, ← finset.prod_attach, finset.prod_congr rfl],
  intros, simp only [finset.coe_mem, finset.mk_coe, dite_eq_ite, if_true],
end

@[simps]
def shift [hr : fact (0 < r)] (k : ℤ) : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_bound (shift_add_monoid_hom k) (r ^ -k)
begin
  abstract shift_spec {
  intro c,
  have H : _ := _,
  refine ⟨H, _⟩,
  { rw continuous_iff,
    intro A,
    let B : finset ℤ := A.map (equiv.to_embedding (equiv.add_left (k:ℤ))),
    let g : laurent_measures_bdd r S B c → laurent_measures_bdd r S A (r ^ -k * c) := λ F,
    { to_fun := λ s a, F s ⟨a+k, _⟩,
      bound' := _, },
    { suffices : truncate A ∘ _ = g ∘ truncate B,
      { rw this, exact continuous_of_discrete_topology.comp (truncate_continuous r S _ B) },
      ext F s a, refl },
    { simp only [finset.mem_map_equiv, equiv.add_left_symm, neg_neg, equiv.coe_add_left,
        neg_add_cancel_comm_assoc, finset.coe_mem], },
    { refine le_trans _ (mul_le_mul' le_rfl F.bound),
      rw [laurent_measures_bdd.nnnorm_def, mul_comm, finset.sum_mul],
      refine finset.sum_le_sum (λ s hs, _),
      simp only [B, finset.univ_eq_attach],
      erw [finset.sum_mul, finset.sum_attach', finset.sum_attach', finset.sum_map],
      refine finset.sum_le_sum (λ n hn, _),
      simp only [finset.mem_map_equiv, equiv.add_left_symm, equiv.coe_add_left, subtype.coe_mk,
        equiv.to_embedding_apply, neg_add_cancel_left],
      simp only [add_comm k, mul_assoc, ← zpow_add₀ hr.out.ne', add_neg_cancel_right], } },
  { intros F hF,
    rw mul_comm,
    refine le_trans _ (mul_le_mul' hF le_rfl),
    simp only [nnnorm_def, finset.sum_mul],
    refine finset.sum_le_sum (λ s _, le_of_eq _),
    transitivity ∑' n, ∥F s n∥₊ * r^n * (r ^ -k),
    { refine ((equiv.add_left (-k:ℤ)).tsum_eq _).symm.trans _,
      simp only [equiv.coe_add_left, shift_add_monoid_hom_apply_to_fun, neg_add_cancel_comm,
        zpow_add₀ hr.out.ne', zpow_neg_one, mul_comm (r ^ -k), mul_assoc], },
    ext,
    simp only [nonneg.coe_mul, nnreal.coe_tsum, coe_nnnorm, nnreal.coe_zpow, tsum_mul_right], } }
end
.

instance [fact (0 < r)] :
  profinitely_filtered_pseudo_normed_group_with_Tinv r (ℒ S) :=
{ Tinv := shift 1,
  Tinv_mem_filtration := λ c F hF, begin
    refine comphaus_filtered_pseudo_normed_group_hom.mk_of_bound_bound_by _ _ _ hF,
    intro c',
    have := @shift.shift_spec r S _ 1 c',
    rwa [zpow_neg_one₀] at this,
  end,
  .. (_: profinitely_filtered_pseudo_normed_group (ℒ S))}

@[simp] lemma Tinv_apply [fact (0 < r)] (F : ℒ S) :
  comphaus_filtered_pseudo_normed_group_with_Tinv.Tinv F = shift 1 F := rfl

variable {α : Type*}

open pseudo_normed_group profinitely_filtered_pseudo_normed_group
  comphaus_filtered_pseudo_normed_group

@[simps]
def map_hom [fact (0 < r)] (f : S ⟶ S') :
  comphaus_filtered_pseudo_normed_group_with_Tinv_hom r (ℒ S) (ℒ S') :=
{ to_fun := map f,
  map_zero' := by { ext, simp only [map_apply, zero_apply, finset.sum_const_zero], },
  map_add' := λ F G, by { ext s i, simp only [←finset.sum_add_distrib, map_apply, add_apply], },
  map_Tinv' := λ F, by { ext s i, simp only [map_apply, Tinv_apply, shift_to_fun_to_fun] },
  strict' := λ c F (hF : ∥F∥₊ ≤ c), (map_bound _ _).trans hF,
  continuous' := λ c, begin
    rw continuous_iff,
    intros T,
    let f₀ : (filtration (laurent_measures r S) c) → (filtration (laurent_measures r S') c) :=
      level (map f) (λ c F (hF : ∥F∥₊ ≤ c), (map_bound f F).trans hF) c,
    have : truncate T ∘ f₀ = laurent_measures_bdd.map f ∘ truncate T, { ext F s' t, refl },
    rw this,
    exact continuous_of_discrete_topology.comp (truncate_continuous r S _ T),
  end }

/--  Let `F : ℒ S` be a Laurent measure.  `laurent_measures.d` chooses a bound `d ∈ ℤ` for `F`,
such that, for all `s : S`, the sequence `F s` is zero from `d-1` and below. -/
def d [h0 : fact (0 < r)] [h1 : fact (r < 1)] (F : ℒ S) : ℤ :=
(exists_bdd_filtration h0.out h1.out F).some

lemma lt_d_eq_zero [h0 : fact (0 < r)] [h1 : fact (r < 1)] (F : ℒ S) (s : S) (n : ℤ) :
  n < F.d → F s n = 0 := (exists_bdd_filtration h0.out h1.out F).some_spec s n

lemma lt_d_eq_zero' [h0 : fact (0 < r)] [h1 : fact (r < 1)] (F : ℒ S) (s : S) (n : ℤ) :
  n < F.d → (F s n : ℝ) = 0 := by exact_mod_cast lt_d_eq_zero F s n

end laurent_measures
