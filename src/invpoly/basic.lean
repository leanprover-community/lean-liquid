import analysis.special_functions.pow
import analysis.special_functions.log
import analysis.specific_limits.basic
import category_theory.Fintype
import analysis.normed_space.basic

import invpoly.bounded
import pseudo_normed_group.basic
import pseudo_normed_group.category

import laurent_measures.basic

import for_mathlib.tsum

universe u

noncomputable theory
open_locale big_operators nnreal classical

def invpoly (r : ℝ≥0) (S : Fintype) := S → polynomial ℤ

variables {r : ℝ≥0} {S S' : Fintype.{u}}

local notation `ℤ[T⁻¹]` := invpoly r

namespace invpoly

instance : has_coe_to_fun (ℤ[T⁻¹] S) (λ F, S → ℕ → ℤ) :=
⟨λ F, λ s n, (F s).coeff n⟩

-- @[simp] lemma coe_mk (f : S → ℕ → ℤ) (hf) (s : S) (n : ℕ) :
--   (@invpoly.mk r S f hf) s n = (f s).coeff n := rfl

@[ext]
lemma ext (F G : ℤ[T⁻¹] S) : (F : S → ℕ → ℤ) = G → F = G :=
by { intros h, funext s, ext, exact congr_fun (congr_fun h s) n }

protected lemma nnreal_summable (F : ℤ[T⁻¹] S) (s : S) :
  summable (λ n, ∥(F s).coeff n∥₊ * r ^ (-n:ℤ)) :=
begin
  apply @summable_of_ne_finset_zero _ _ _ _ _ (F s).support,
  intros n hn,
  simp only [polynomial.mem_support_iff, not_not] at hn,
  simp only [hn, nnnorm_zero, zero_mul],
end

protected lemma summable (F : ℤ[T⁻¹] S) (s : S) :
  summable (λ n, ∥(F s).coeff n∥ * r ^ (-n : ℤ)) :=
begin
  simpa only [← nnreal.summable_coe, nnreal.coe_mul, coe_nnnorm, nnreal.coe_zpow]
    using F.nnreal_summable s
end

-- Move me
lemma nonneg_of_norm_mul_zpow (k n : ℤ) (r : ℝ≥0) : 0 ≤ ∥ k ∥ * (r : ℝ)^n :=
mul_nonneg (norm_nonneg _) (zpow_nonneg (nnreal.coe_nonneg _) _)

def map (f : S ⟶ S') : ℤ[T⁻¹] S → ℤ[T⁻¹] S' := λ F,
λ s', ∑ s in finset.univ.filter (λ t, f t = s'), F s

@[simp] lemma map_apply (f : S ⟶ S') (F : ℤ[T⁻¹] S) (s' : S') (k : ℕ) :
  (map f F s').coeff k = ∑ s in finset.univ.filter (λ t, f t = s'), (F s).coeff k :=
begin
  simp only [map, polynomial.coeff_sum],
  sorry
end

@[simp] lemma map_id : (map (𝟙 S) : ℤ[T⁻¹] S → ℤ[T⁻¹] S) = id :=
begin
  ext F s k,
  simp only [map_apply, Fintype.id_apply, id.def, finset.sum_filter,
    finset.sum_ite_eq', finset.mem_univ, if_true],
  sorry
end

@[simp] lemma map_comp {S'' : Fintype.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
  (map (f ≫ g) : ℤ[T⁻¹] S → ℤ[T⁻¹] S'') = map g ∘ map f :=
begin
  ext F s k,
  simp only [function.comp_app, map_apply, finset.sum_congr],
  sorry
  -- rw ← finset.sum_bUnion,
  -- { apply finset.sum_congr,
  --   { change finset.univ.filter (λ t, g (f t) = s) = _,
  --     ext i,
  --     split;
  --     { intro hi, simpa only [finset.mem_bUnion, finset.mem_filter, finset.mem_univ, true_and,
  --         exists_prop, exists_eq_right'] using hi } },
  --   { intros, refl } },
  -- { intros i hi j hj h k hk,
  --   simp only [finset.inf_eq_inter, finset.mem_inter, finset.mem_filter, finset.mem_univ, true_and,
  --     finset.coe_filter, finset.coe_univ, set.sep_univ, set.mem_set_of_eq] at hi hj hk,
  --   refine h _,
  --   rw [← hk.1, ← hk.2] }
end

instance : add_comm_group (ℤ[T⁻¹] S) :=
by { delta invpoly, apply_instance }.

instance : has_norm (ℤ[T⁻¹] S) :=
⟨λ F, ∑ s, ∑' n, ∥(F s).coeff n∥ * (r : ℝ) ^ (-n:ℤ)⟩

lemma norm_def (F : ℤ[T⁻¹] S) : ∥F∥ = ∑ s, ∑' n, ∥(F s).coeff n∥ * (r : ℝ)^(-n:ℤ) := rfl

instance : has_nnnorm (ℤ[T⁻¹] S) :=
⟨λ F, ∑ s, ∑' n, ∥(F s).coeff n∥₊ * r ^ (-n : ℤ)⟩

lemma nnnorm_def (F : ℤ[T⁻¹] S) : ∥F∥₊ = ∑ s, ∑' n, ∥(F s).coeff n∥₊ * r^(-n:ℤ) := rfl

@[simp] lemma coe_nnnorm (F : ℤ[T⁻¹] S) : (∥F∥₊ : ℝ) = ∥F∥ :=
by simp only [nnnorm_def, norm_def, nnreal.coe_sum, nnreal.coe_tsum,
  nonneg.coe_mul, coe_nnnorm, nnreal.coe_zpow]

@[simp] lemma invpoly.norm_nonneg (F : ℤ[T⁻¹] S) : 0 ≤ ∥F∥ :=
by rw [← coe_nnnorm]; exact ∥F∥₊.coe_nonneg

@[simp] lemma nnnorm_neg (F : ℤ[T⁻¹] S) : ∥-F∥₊ = ∥F∥₊ :=
by simp only [nnnorm_def, neg_apply, nnnorm_neg]

lemma nnnorm_add (F G : ℤ[T⁻¹] S) : ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
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

lemma norm_add (F G : ℤ[T⁻¹] S) : ∥F + G∥ ≤ ∥F∥ + ∥G∥ :=
by simpa only [← coe_nnnorm, ← nnreal.coe_add, nnreal.coe_le_coe] using nnnorm_add F G

@[simp] lemma nsmul_apply (k : ℕ) (F : ℤ[T⁻¹] S) (s : S) (n : ℕ) : (k • F) s n = k • ((F s).coeff n) := rfl

@[simp] lemma zsmul_apply (k : ℤ) (F : ℤ[T⁻¹] S) (s : S) (n : ℕ) : (k • F) s n = k • ((F s).coeff n) := rfl

section
open finset

lemma map_bound (f : S ⟶ S') (F : ℤ[T⁻¹] S) : ∥map f F∥₊ ≤ ∥F∥₊ := calc
∥map f F∥₊ = ∑ s', ∑' n, ∥∑ s in univ.filter (λ t, f t = s'), (F s).coeff n∥₊ * _ : rfl
... ≤ ∑ s', ∑' n, ∑ s in univ.filter (λ t, f t = s'), ∥(F s).coeff n∥₊ * r^(-n:ℤ) : begin
  apply sum_le_sum,
  rintros s' -,
  have h1 : summable (λ n : ℕ, ∑ (s : S.α) in univ.filter (λ t, f t = s'), ∥(F s).coeff n∥₊ * r^(-n:ℤ)) :=
    summable_sum (λ s _, F.nnreal_summable s),
  have h2 : ∀ b : ℕ,
    ∥∑ (s : S.α) in univ.filter (λ t, f t = s'), F s b∥₊ * r ^ (-b:ℤ) ≤
      ∑ (s : S.α) in univ.filter (λ t, f t = s'), ∥F s b∥₊ * r ^ (-b:ℤ),
  { intros b, rw ← sum_mul, exact mul_le_mul' (nnnorm_sum_le _ _) le_rfl },
  apply tsum_le_tsum h2 (nnreal.summable_of_le h2 h1) h1,
end
... = ∑ s', ∑ s in univ.filter (λ t, f t = s'), ∑' n, ∥(F s).coeff n∥₊ * r^(-n:ℤ) :
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

lemma map_bound' (f : S ⟶ S') (F : ℤ[T⁻¹] S) : ∥map f F∥ ≤ ∥F∥ :=
by simpa only [← coe_nnnorm, ← nnreal.coe_add, nnreal.coe_le_coe] using map_bound f F

/-- This lemma puts bounds on where `(F s).coeff n` can be nonzero. -/
lemma eq_zero_of_filtration (F : ℤ[T⁻¹] S) (c : ℝ≥0) :
  ∥F∥₊ ≤ c → ∀ (s : S) (n : ℕ), c < r^(-n:ℤ) → (F s).coeff n = 0 :=
begin
  intros h(F s).coeff n h,
  suffices : ∥(F s).coeff n∥₊ < 1,
  { change abs ((F s).coeff n : ℝ) < 1 at this,
    norm_cast at this,
    rwa ← int.eq_zero_iff_abs_lt_one },
  have : ∥(F s).coeff n∥₊ * r ^ (-n : ℤ) ≤ ∑' k, ∥(F s).coeff k∥₊ * r ^ (-k:ℤ),
  { exact le_tsum (F.nnreal_summable s) _ (λ k _, zero_le'), },
  replace this := lt_of_le_of_lt (this.trans _) h,
  { have hr₁ : 0 < r^(-n:ℤ) := lt_of_le_of_lt zero_le' h,
    have hr₂ : r^(-n:ℤ) ≠ 0 := hr₁.ne',
    convert mul_lt_mul this (le_refl (r ^ (-n : ℤ))⁻¹) _ hr₁.le,
    { exact (mul_inv_cancel_right₀ hr₂ _).symm },
    { exact (mul_inv_cancel hr₂).symm },
    { rwa nnreal.inv_pos }, },
  { refine le_trans _ hF,
    apply @finset.single_le_sum S ℝ≥0 _ (λ s, ∑' n, ∥(F s).coeff n∥₊ * r^(-n:ℤ)),
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

-- --For every F, d F is a bound whose existence is established in `eq_zero_of_filtration`
-- lemma exists_bdd_filtration {S : Fintype} (hr₀ : 0 < (r : ℝ)) (hr₁ : (r : ℝ) < 1) (F : ℤ[T⁻¹] S) :
--   ∃ d : ℕ, ∀ s : S, ∀ (n : ℕ), n < d → (F s).coeff n = 0 :=
-- begin
--   have h_logr : (log r) < 0 := log_neg hr₀ hr₁,
--   let d := if log ∥ F ∥ ≥ 0 then ⌊ (log ∥ F ∥ / log (r : ℝ)) ⌋ - 1 else -1,
--   use d,
--   intros s n hn,
--   have H1 := zpow_strict_anti hr₀ hr₁ hn,
--   suffices H2 : ∥F∥₊ < r ^ d,
--   { refine eq_zero_of_filtration F (∥F∥₊) le_rfl s n (H2.trans _),
--     rw [← nnreal.coe_lt_coe, nnreal.coe_zpow, nnreal.coe_zpow],
--     exact zpow_strict_anti hr₀ hr₁ hn, },
--   have hd1 : 0 < -(d : ℝ),
--   { rw [lt_neg, neg_zero, ← int.cast_zero, int.cast_lt],
--     apply int.lt_of_le_sub_one,
--     dsimp only [d],
--     split_ifs,
--     { rw [tsub_le_iff_right, sub_add, sub_self, sub_zero],
--       exact int.floor_nonpos (div_nonpos_of_nonneg_of_nonpos h(le_of_lt h_logr)) },
--     { simp only [zero_sub] } },
--   have hFd1 : (log ∥ F ∥) < d * (log (r : ℝ)),
--   { rw ← zsmul_eq_mul,
--     rw ite_smul,
--     split_ifs,
--     { rw zsmul_eq_mul,
--       calc (log ∥F∥)
--           = (log ∥F∥/log r) * log r : (div_mul_cancel (log ∥F∥) (ne_of_lt h_logr)).symm
--       ... ≤ ⌊ (log ∥F∥)/log r⌋ * log r : (mul_le_mul_right_of_neg h_logr).mpr (int.floor_le _)
--       ... < (⌊ (log ∥F∥)/log r⌋ - 1) * log r : (mul_lt_mul_right_of_neg h_logr).mpr (sub_one_lt _)
--       ... = ↑(⌊ (log ∥F∥)/log r⌋ - 1) * log r : by simp only [int.cast_one, int.cast_sub] },
--     { rw [neg_smul, one_smul],
--       rw [ge_iff_le, not_le] at h,
--       apply h.trans,
--       rwa [lt_neg, neg_zero] } },
--   rw [← nnreal.coe_lt_coe, nnreal.coe_zpow, coe_nnnorm],
--   have := (real.lt_rpow_of_log_lt (invpoly.norm_nonneg F) hr₀ hFd1),
--   rwa [real.rpow_int_cast _ d] at this,
-- end

section profinite_structure

@[simps] def truncate {c : ℝ≥0} (A : finset ℕ) :
  { F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c } → invpoly_bdd r S A c := λ F,
{ to_fun := λ s i, F s i,
  bound' := begin
    refine (finset.sum_le_sum $ λ s _, _).trans F.2,
    convert sum_le_tsum A _ ((F : ℤ[T⁻¹] S).nnreal_summable s) using 1,
    { conv_rhs { rw ← finset.sum_attach }, refl },
    { intros b hb, exact zero_le', },
  end }

lemma eq_iff_truncate_eq (c : ℝ≥0) (F G : {F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c}) :
  (∀ k, truncate k F = truncate k G) → F = G :=
begin
  intros h,
  ext s i,
  specialize h {i},
  apply_fun (λ e, e s ⟨i, by simp⟩) at h,
  exact h,
end


def finset_map {A B : finset ℕ} (h : B ≤ A) : B → A :=
λ i, ⟨i, h i.2⟩

def transition {c : ℝ≥0} {A B : finset ℕ} (h : B ≤ A) :
  invpoly_bdd r S A c → invpoly_bdd r S B c := λ F,
⟨λ s i, F s (finset_map h i), begin
  refine (finset.sum_le_sum $ λ s _, _).trans F.2,
  have : ∑ i : B, ∥F s (finset_map h i)∥₊ * r^(-i : ℤ) =
    ∑ i in finset.univ.image (finset_map h), ∥F s i∥₊ * r^(-i : ℤ),
  { rw finset.sum_image,
    { refl },
    { rintros i - j - hh,
      apply subtype.ext,
      apply_fun (λ e, e.val) at hh,
      exact hh } },
  rw this,
  refine finset.sum_le_sum_of_subset_of_nonneg (finset.subset_univ _) (λ _ _ _, zero_le'),
end⟩

def mk_seq {c} (F : Π (A : finset ℕ), invpoly_bdd r S A c) :
  S → ℕ → ℤ := λ s i, F {i} s ⟨i, by simp⟩

lemma mk_seq_compat {c} (F : Π (A : finset ℕ), invpoly_bdd r S A c)
  (compat : ∀ (A B : finset ℕ) (h : B ≤ A), transition h (F _) = F _) (s : S)
  (A : finset ℕ) (i : A) : mk_seq F s i = F A s i :=
begin
  have : ({i} : finset ℕ) ≤ A, { simp },
  specialize compat _ _ this,
  dsimp [mk_seq],
  rw ← compat,
  change (F A) s _ = _,
  congr,
  ext,
  refl,
end

lemma mk_seq_compat_summable {c} (F : Π (A : finset ℕ), invpoly_bdd r S A c)
  (compat : ∀ (A B : finset ℕ) (h : B ≤ A), transition h (F _) = F _) (s : S) :
  summable (λ k : ℕ, ∥mk_seq (F s).coeff k∥ * (r:ℝ)^(-k:ℤ)) :=
begin
  apply summable_of_sum_le,
  { intro k,
    dsimp,
    refine mul_nonneg (norm_nonneg _) (zpow_nonneg (nnreal.coe_nonneg _) _) },
  { intros A,
    rw ← finset.sum_attach,
    refine le_trans _ (F A).bound,
    simp_rw mk_seq_compat _ compat,
    simp only [invpoly_bdd.nnnorm_def, finset.univ_eq_attach, nnreal.coe_sum,
      nnreal.coe_mul, nnreal.coe_zpow],
    apply @finset.single_le_sum S ℝ _ (λ s, ∑ (i : A), ∥ F A s i ∥ * (r : ℝ)^(-i : ℤ)),
    swap, { simp },
    rintro s -,
    apply finset.sum_nonneg,
    rintros a -,
    refine mul_nonneg (norm_nonneg _) (zpow_nonneg (nnreal.coe_nonneg _) _) },
end

lemma mk_seq_compat_nnreal_summable {c} (F : Π (A : finset ℕ), invpoly_bdd r S A c)
  (compat : ∀ (A B : finset ℕ) (h : B ≤ A), transition h (F _) = F _) (s : S) :
  summable (λ k : ℕ, ∥mk_seq (F s).coeff k∥₊ * r^(-k:ℤ)) :=
begin
  rw ← nnreal.summable_coe,
  simpa only [nonneg.coe_mul, coe_nnnorm, nnreal.coe_zpow] using mk_seq_compat_summable F compat s
end

lemma mk_seq_compat_sum_le {c} (F : Π (A : finset ℕ), invpoly_bdd r S A c)
  (compat : ∀ (A B : finset ℕ) (h : B ≤ A), transition h (F _) = F _)  :
  ∑ (s : S), ∑' (k : ℕ), ∥mk_seq (F s).coeff k∥₊ * r^(-k:ℤ) ≤ c :=
begin
  rw ← tsum_sum,
  swap, { intros s hs, apply mk_seq_compat_nnreal_summable _ compat },
  have : ∀ A : finset ℕ,
    ∑ (b : A), ∑ (s : S), ∥F A s b∥₊ * r^(-b : ℤ) ≤ c,
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

lemma exists_of_compat {c} (F : Π (A : finset ℕ), invpoly_bdd r S A c)
  (compat : ∀ (A B : finset ℕ) (h : B ≤ A),
    transition h (F _) = F _) :
  ∃ (G : {H : ℤ[T⁻¹] S | ∥H∥₊ ≤ c }), ∀ (k : finset ℕ), truncate k G = F k :=
begin
  let G : ℤ[T⁻¹] S := ⟨mk_seq F, mk_seq_compat_nnreal_summable _ compat⟩,
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
def invpoly_bdd_functor (c : ℝ≥0) [fact (0 < r)] :
  (as_small (finset ℕ))ᵒᵖ ⥤ Fintype :=
{ obj := λ A, Fintype.of $ invpoly_bdd r S (ulift.down A.unop) c,
  map := λ A B f, transition (le_of_hom $ ulift.down f.unop) }.

def invpoly_bdd_equiv (c : ℝ≥0) [fact (0 < r)] : { F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c } ≃
  (Profinite.limit_cone (invpoly_bdd_functor r S c ⋙ Fintype.to_Profinite)).X :=
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

instance (c : ℝ≥0) [fact (0 < r)] : topological_space {F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c} :=
topological_space.induced (invpoly_bdd_equiv r S c) infer_instance

def invpoly_bdd_homeo (c : ℝ≥0) [fact (0 < r)] : { F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c } ≃ₜ
  (Profinite.limit_cone (invpoly_bdd_functor r S c ⋙ Fintype.to_Profinite)).X :=
{ continuous_to_fun := continuous_induced_dom,
  continuous_inv_fun := begin
    have : inducing (invpoly_bdd_equiv r S c) := ⟨rfl⟩,
    rw this.continuous_iff,
    dsimp,
    simp only [equiv.self_comp_symm],
    exact continuous_id,
  end,
  ..(invpoly_bdd_equiv _ _ _) }

instance (c : ℝ≥0) [fact (0 < r)] : t2_space { F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c } :=
(invpoly_bdd_homeo r S c).symm.t2_space

instance (c : ℝ≥0) [fact (0 < r)] : totally_disconnected_space { F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c } :=
(invpoly_bdd_homeo r S c).symm.totally_disconnected_space

instance (c : ℝ≥0) [fact (0 < r)] : compact_space {F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c} :=
(invpoly_bdd_homeo r S c).symm.compact_space

@[continuity]
lemma truncate_continuous (c : ℝ≥0) [fact (0 < r)] (A : finset ℕ) :
  continuous (truncate A : _ → invpoly_bdd r S _ c) :=
begin
  let g₁ :=
    (Profinite.limit_cone (invpoly_bdd_functor.{u} r S c ⋙ Fintype.to_Profinite)).π.app
    (opposite.op $ ulift.up A),
  let g₂ := (invpoly_bdd_homeo r S c),
  change continuous (g₁ ∘ g₂),
  continuity,
end

lemma continuous_iff (c : ℝ≥0) [fact (0 < r)] {α : Type*} [topological_space α]
  (f : α → { F : ℤ[T⁻¹] S | ∥F∥₊ ≤ c }) :
  continuous f ↔ ∀ (A : finset ℕ), continuous ((truncate A) ∘ f) :=
begin
  split,
  { intros hf A, continuity },
  { intros h,
    rw ← (invpoly_bdd_homeo r S c).comp_continuous_iff,
    apply continuous_subtype_mk,
    apply continuous_pi,
    intros A,
    apply h }
end

end profinite_structure

--needed?
instance : pseudo_normed_group (ℤ[T⁻¹] S) :=
{ filtration := λ c, { F | ∥F∥₊ ≤ c },
  filtration_mono := λ c₁ c₂ h F hF, by {dsimp at *, exact le_trans hF h},
  zero_mem_filtration := λ c, by simp [nnnorm_def],
  neg_mem_filtration := λ c F h, (nnnorm_neg F).le.trans h,
  add_mem_filtration := λ c₁ c₂ F₁ F₂ h₁ h₂, (nnnorm_add _ _).trans (add_le_add h₁ h₂) }

@[simp] lemma mem_filtration_iff (F : ℤ[T⁻¹] S) (c : ℝ≥0) :
  F ∈ pseudo_normed_group.filtration (ℤ[T⁻¹] S) c ↔ ∥F∥₊ ≤ c := iff.rfl

instance [fact (0 < r)] : profinitely_filtered_pseudo_normed_group (ℤ[T⁻¹] S) :=
{ continuous_add' := begin
    intros c₁ c₂,
    rw continuous_iff,
    intros A,
    let E : invpoly_bdd r S A c₁ × invpoly_bdd r S A c₂ →
      invpoly_bdd r S A (c₁ + c₂) := λ G, ⟨G.1 + G.2, _⟩,
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
      (truncate A : _ → invpoly_bdd r S A (c₁ + c₂)) ∘ pseudo_normed_group.add' =
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
    let E : invpoly_bdd r S A c → invpoly_bdd r S A c :=
      λ G, ⟨- G, _⟩,
    swap, {
      convert G.2 using 1,
      apply finset.sum_congr rfl,
      intros s hs,
      apply finset.sum_congr rfl,
      intros x hx,
      congr' 1,
      simpa },
    have : (truncate A : _ → invpoly_bdd r S A c) ∘ pseudo_normed_group.neg' =
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
    let g : invpoly_bdd r S A c₁ → invpoly_bdd r S A c₂ :=
      λ g, ⟨g, le_trans g.2 h.out⟩,
    have : (truncate A : _ → invpoly_bdd r S A c₂) ∘ pseudo_normed_group.cast_le =
      g ∘ truncate A,
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply truncate_continuous }
  end,
  ..(infer_instance : (pseudo_normed_group (ℤ[T⁻¹] S))) }
.

def Tinv_aux {R : Type*} [has_zero R] : (ℕ → R) → ℕ → R
| F 0     := 0
| F (n+1) := F n

@[simp] lemma Tinv_aux_zero {R : Type*} [has_zero R] (f : ℕ → R) : Tinv_aux f 0 = 0 := rfl

@[simp] lemma Tinv_aux_ne_zero {R : Type*} [has_zero R] (f : ℕ → R) (i : ℕ) (hi : i ≠ 0) :
  Tinv_aux f i = f (i - 1) :=
by { cases i, contradiction, refl, }

@[simp] lemma Tinv_aux_succ {R : Type*} [has_zero R] (f : ℕ → R) (i : ℕ) :
  Tinv_aux f (i + 1) = f i :=
rfl

lemma Tinv_aux_summable [hr : fact (0 < r)] (F : ℤ[T⁻¹] S) (s : S) :
  summable (λ n, (∥(Tinv_aux (F s) n)∥₊ * r ^ (-n:ℤ))) :=
begin
  rw ← nnreal.summable_nat_add_iff 1,
  simp only [Tinv_aux_succ, int.coe_nat_succ, neg_add, zpow_add₀ hr.out.ne', ← mul_assoc],
  apply summable.mul_right,
  exact F.nnreal_summable s,
end

/--
The `T⁻¹` action on `ℤ[T⁻¹] S`.
This is defined, essentially, as a shift in `ℕ` (accounting for the restriction at 0).
This is an additive group homomorphism.
-/
def Tinv_add_monoid_hom {S : Fintype.{u}} [hr : fact (0 < r)] :
  ℤ[T⁻¹] S →+ ℤ[T⁻¹] S :=
add_monoid_hom.mk' (λ F,
  { to_fun := λ s, Tinv_aux (F s),
    summable' := λ s, Tinv_aux_summable F s })
  (by { intros F G, ext s (_|n); refl })

@[simps]
def Tinv [hr : fact (0 < r)] :
  comphaus_filtered_pseudo_normed_group_hom (ℤ[T⁻¹] S) (ℤ[T⁻¹] S) :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_bound Tinv_add_monoid_hom r⁻¹
begin
  abstract Tinvt_spec {
  intro c,
  have H : _ := _,
  refine ⟨H, _⟩,
  { rw continuous_iff,
    intro A,
    let B : finset ℕ := A.image (λ k, k - 1),
    have hB : ∀ a : A, (a:ℕ) - 1 ∈ B,
    { intro, simp only [finset.mem_image], refine ⟨a, a.2, rfl⟩ },
    let C : finset ℕ := B.map ⟨_, add_left_injective 1⟩,
    have hAC : A ⊆ insert 0 C,
    { rintro (_|a) ha,
      { exact finset.mem_insert_self _ _, },
      { refine finset.mem_insert_of_mem _,
        simp only [finset.mem_map, finset.mem_image, exists_prop, function.embedding.coe_fn_mk,
          exists_exists_and_eq_and],
        refine ⟨a.succ, ha, rfl⟩ } },
    -- let ψ : Π (A : finset ℕ), S → A → ℤ,
    -- { rintros A s ⟨(_|a), ha⟩, exact 0, exact F s ⟨a, hB ⟨_, ha⟩⟩ },
    let g : invpoly_bdd r S B c → invpoly_bdd r S A (r⁻¹ * c) := λ F,
    { to_fun := λ s a, _,
      bound' := _, },
    swap 2, { cases a with a ha, cases a, exact 0, exact F s ⟨a, hB ⟨_, ha⟩⟩ },
    { suffices : truncate A ∘ _ = g ∘ truncate B,
      { rw this, exact continuous_of_discrete_topology.comp (truncate_continuous r S _ B) },
      ext F s ⟨(_|a), ha⟩; refl },
    { refine le_trans _ (mul_le_mul' le_rfl F.bound),
      rw [invpoly_bdd.nnnorm_def, mul_comm, finset.sum_mul],
      refine finset.sum_le_sum (λ s hs, _),
      simp only [B, finset.univ_eq_attach],
      erw [finset.sum_mul, finset.sum_attach', finset.sum_attach'],
      refine (finset.sum_le_sum_of_subset hAC).trans _,
      have h0C : 0 ∉ C,
      { simp only [finset.mem_map, function.embedding.coe_fn_mk, nat.succ_ne_zero,
          exists_false, not_false_iff], },
      rw [finset.sum_insert h0C],
      simp only [function.embedding.coe_fn_mk, finset.mem_image, exists_prop, nat.rec_zero,
        nnnorm_zero, coe_coe, subtype.coe_mk, zero_mul, dite_eq_ite, if_t_t, zpow_neg₀,
        zpow_coe_nat, finset.sum_map, nat.rec_add_one, zero_add],
      refine finset.sum_le_sum (λ n hn, _),
      split_ifs with h₁ h₂, rotate,
      { exact (h₂ ⟨n+1, h₁, rfl⟩).elim },
      { exact zero_le' },
      { exact zero_le' },
      simp only [pow_add, mul_inv₀, pow_one, mul_assoc],
      exact le_rfl } },
  { intros F hF,
    rw mul_comm,
    refine le_trans _ (mul_le_mul' hF le_rfl),
    simp only [nnnorm_def, finset.sum_mul],
    refine finset.sum_le_sum (λ s _, _),
    transitivity ∑' n, ∥(F s).coeff n∥₊ * r^(-n:ℤ) * r⁻¹,
    { rw ← sum_add_tsum_nat_add' 1,
      swap, { apply Tinv_aux_summable },
      simp only [finset.range_one, zpow_neg₀, zpow_coe_nat, finset.sum_singleton,
        pow_zero, inv_one, mul_one, int.coe_nat_succ, neg_add, zpow_add₀ hr.out.ne',
        zpow_one, mul_assoc, Tinv_add_monoid_hom, add_monoid_hom.mk'_apply,
        coe_mk, Tinv_aux_zero, nnnorm_zero, Tinv_aux_succ, zero_add], },
    refine le_of_eq _, ext,
    simp only [nonneg.coe_mul, nnreal.coe_tsum, coe_nnnorm, nnreal.coe_zpow, tsum_mul_right], } }
end
.

instance [fact (0 < r)] :
  profinitely_filtered_pseudo_normed_group_with_Tinv r (ℤ[T⁻¹] S) :=
{ Tinv := Tinv,
  Tinv_mem_filtration := λ c F hF,
    comphaus_filtered_pseudo_normed_group_hom.mk_of_bound_bound_by _ _ _ hF,
  .. (_: profinitely_filtered_pseudo_normed_group (ℤ[T⁻¹] S))}

variable {α : Type*}

open pseudo_normed_group profinitely_filtered_pseudo_normed_group
  comphaus_filtered_pseudo_normed_group

@[simps]
def map_hom [fact (0 < r)] (f : S ⟶ S') :
  comphaus_filtered_pseudo_normed_group_with_Tinv_hom r (ℤ[T⁻¹] S) (ℤ[T⁻¹] S') :=
{ to_fun := map f,
  map_zero' := by { ext, simp only [map_apply, zero_apply, finset.sum_const_zero], },
  map_add' := λ F G, by { ext s i, simp only [←finset.sum_add_distrib, map_apply, add_apply], },
  map_Tinv' := λ F, by { ext s (_|i); simp only [map_apply]; sorry },
  strict' := λ c F (hF : ∥F∥₊ ≤ c), (map_bound _ _).trans hF,
  continuous' := λ c, begin
    rw continuous_iff,
    intros T,
    let f₀ : (filtration (invpoly r S) c) → (filtration (invpoly r S') c) :=
      level (map f) (λ c F (hF : ∥F∥₊ ≤ c), (map_bound f F).trans hF) c,
    have : truncate T ∘ f₀ = invpoly_bdd.map f ∘ truncate T, { ext F s' t, refl },
    rw this,
    exact continuous_of_discrete_topology.comp (truncate_continuous r S _ T),
  end }

end invpoly
