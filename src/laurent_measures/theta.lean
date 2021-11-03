import category_theory.Fintype
import data.real.nnreal
import laurent_measures.basic
import order.filter.at_top_bot
import pseudo_normed_group.basic
import pseudo_normed_group.category
import real_measures
import ring_theory.principal_ideal_domain

/-- SECTIONS
Everything takes place in the `namespace theta`

* Section `aux_lemmas` contain some technicalities concerning convergent sequence
* Section `summability` shows that the series defining `θ` converges
* In Section `theta_surjective` We define the map θ : (laurent_measures r `singleton`) → ℝ and we
  show it is surjective.
* Section `ker_theta` studies the kernel of `θ`, in particular showing it is principal.

   VARIABLES
* The variable `ξ : ℝ` here corresponds to `r'` of `Analytic.pdf`, so that, for every `r`, `θ ξ` is
`θ_r'` as a map from `r`-convergent Laurent measures to `ℝ`. It is supposed to be positive almost
everywhere, and this is recorded as a `fact`.
* The variable `x : ℝ` is defined globally in Sections `aux_lemmas` and `summability`.
* The variable `r : ℝ≥0` (specifying the radius of convergency of `laurent_measures` makes its
  first appearance in Section `theta_surjective`, but it is not globally defined. Whenever it occurs
  it is assumed to be positive and strictly smaller than `1`, both recorded as facts.
-/

noncomputable theory

open set filter function classical finset nat
open_locale topological_space classical nnreal big_operators

def laurent_measures.to_Rfct (r : ℝ≥0) :
  (laurent_measures r (Fintype.of punit)) → (ℤ → ℤ) := λ ⟨F, _⟩, (F punit.star)

namespace theta

variable (ξ : ℝ)

/--The basic function computing the **integer-valued** `ξ`-adic expansion of `x` -/
noncomputable def y (x : ℝ) : ℕ → ℝ
| 0         := x
| (n + 1)   := (y n) - (⌊(((y n) / ξ ^ n) : ℝ)⌋ : ℝ) * ξ ^ n

section aux_lemmas

variable (x : ℝ)
variable [fact (0 < ξ)]

lemma bdd_floor : bdd_above (range (λ n : ℕ, (⌊ y ξ x n / ξ ^ n⌋ : ℝ))) :=
begin
  use (max x ξ ⁻¹ : ℝ),
  intros z hz,
  obtain ⟨m, h_mz⟩ := (set.mem_range).mp hz,
    by_cases hm : m = 0,
  { rw [hm, pow_zero, div_one] at h_mz,
    rw [← h_mz, y, le_max_iff],
    apply or.intro_left,
    exact int.floor_le x },
  rw ← h_mz,
  apply (int.floor_le _).trans,
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k + 1 := nat.exists_eq_succ_of_ne_zero hm,
  rw [hk, y],
  have : ξ ^ k ≠ 0 := ne_of_gt (pow_pos (fact.out _) k),
  calc (y ξ x k - ↑⌊y ξ x k / ξ ^ k⌋ * ξ ^ k) / ξ ^ (k + 1) =
              (y ξ x k - ↑⌊y ξ x k / ξ ^ k⌋ * ξ ^ k) / (ξ ^ k * ξ) : by {rw [pow_add, pow_one]}
        ... = (y ξ x k - ↑⌊y ξ x k / ξ ^ k⌋ * ξ ^ k) / ξ ^ k / ξ : by {field_simp}
        ... = (y ξ x k / ξ ^ k - ↑⌊y ξ x k / ξ ^ k⌋ * ξ ^ k / ξ ^ k) / ξ : by {rw [sub_div]}
        ... = (y ξ x k / ξ ^ k - ↑⌊y ξ x k / ξ ^ k⌋) / ξ : by {simp only [mul_div_cancel,
                                                                      this, ne.def, not_false_iff]}
        ... ≤ 1 / ξ : div_le_div_of_le (le_of_lt _) (le_of_lt _)
        ... ≤ max x ξ ⁻¹ : by {field_simp},
  exact fact.out _,
  {rw [sub_lt_iff_lt_add, add_comm], from (int.lt_floor_add_one _)},
end

lemma eventually_pos_y : ∀ n : ℕ, n ≥ 1 → y ξ x n ≥ 0 :=
begin
  have h_pos : ∀ n : ℕ, n ≥ 1 → ξ ^ n > 0 := λ n _, pow_pos (fact.out _) n,
  have : ∀ n : ℕ, n ≥ 1 →  (y ξ x n) / ξ ^ n ≥ ⌊(((y ξ x n) / ξ ^ n) : ℝ)⌋ := λ n _, int.floor_le _,
  intros n hn₁,
  by_cases hn₀ : n = 1,
  { rw [hn₀, y,pow_zero, div_one, mul_one, ge_iff_le, sub_nonneg], apply int.floor_le },
  { replace hn₁ : n > 1, {apply (lt_of_le_of_ne hn₁), tauto },
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m ≥ 1 ∧ n = m + 1,
    use ⟨n - 1, and.intro (nat.le_pred_of_lt hn₁) (nat.sub_add_cancel (le_of_lt hn₁)).symm⟩,
    rw [hm.2, y],
    replace this := (le_div_iff (h_pos m hm.1)).mp (this m hm.1),
    rwa ← sub_nonneg at this },
end

lemma eventually_pos_floor : ∀ n : ℕ, n ≥ 1 → (⌊((y ξ x n) / ξ ^ n )⌋ : ℝ) ≥ 0 :=
begin
  have h_pos : ∀ n : ℕ, n ≥ 1 → ξ ^ n > 0 := λ n _, pow_pos (fact.out _) n,
  intros n hn,
  norm_cast,
  apply int.floor_nonneg.mpr,
  exact div_nonneg (eventually_pos_y ξ x n hn) (le_of_lt (h_pos n hn)),
end

lemma eventually_le : ∀ n, n ≥ 1 → y ξ x (n + 1) ≤ (y ξ x n) :=
begin
  have h_pos : ∀ n : ℕ, n ≥ 1 → ξ ^ n > 0 := λ n _, pow_pos (fact.out _) n,
  intros n hn,
  rw y,
  apply sub_le_self (y ξ x n),
  apply mul_nonneg _ (le_of_lt (h_pos n hn)),
  exact eventually_pos_floor ξ x n hn,
end

lemma eventually_le_one {n : ℕ} (hn : n ≥ 1) : (y ξ x n) ≤ (y ξ x 1) :=
begin
  induction hn with n hn h_ind,
  exact le_of_eq (refl _),
  have := (eventually_le ξ x n hn).trans h_ind,
  rwa nat.succ_eq_add_one,
end

def aux_y : ℕ → ℝ := λ n, if n = 0 then y ξ x 1 else y ξ x n

lemma eventually_antitone : antitone (aux_y ξ x) :=
begin
  apply antitone_nat_of_succ_le,
  intro n,
  by_cases hn : n = 0,
  {rw [hn, zero_add, aux_y],
    simp only [nat.one_ne_zero, if_true, eq_self_iff_true, if_false] },
  { simp only [aux_y, if_neg hn, function.comp_app, nat.succ_ne_zero, if_false],
    replace hn : n ≥ 1 := le_of_not_gt ((not_iff_not.mpr nat.lt_one_iff).mpr hn),
    exact eventually_le ξ x n hn },
end

lemma limit_neg_geometric [fact (ξ < 1)] : tendsto (λ i : ℕ, - ξ ^ i) at_top (𝓝 0) :=
begin
  apply summable.tendsto_at_top_zero,
  rw summable_neg_iff,
  apply summable_geometric_of_abs_lt_1,
  rw abs_of_pos,
  all_goals {exact fact.out _},
end

end aux_lemmas

section summability

variable (x : ℝ)

lemma finite_sum (n : ℕ) : (y ξ x (n + 1) : ℝ) =
  x - ∑ i in range(n + 1),  (⌊(((y ξ x i) / ξ ^ i) : ℝ)⌋ : ℝ) * (ξ ^ i) :=
begin
  induction n with n h_ind,
  { rw [zero_add, range_one, sum_singleton], refl },
  { replace h_ind : (x - (y ξ x (n + 1)) : ℝ) =
    ∑ i in range(n + 1),  (⌊(y ξ x i / ξ ^ i : ℝ)⌋ : ℝ) * ξ ^ i := by {rw [sub_eq_iff_eq_add,
      ← sub_eq_iff_eq_add', h_ind] },
    nth_rewrite_rhs 2 [nat.succ_eq_add_one, ← nat.succ_eq_add_one, range_succ],
    rw [sum_insert, nat.succ_eq_add_one, ← sub_sub, ← h_ind, sub_sub, add_sub, add_comm _ x,
      ← add_sub, ← sub_sub, sub_self, zero_sub, neg_sub],
    refl,
    simp },
end

lemma finite_sum' (n : ℕ) : x - (y ξ x n : ℝ) =
  ∑ i in range (n),  (⌊(((y ξ x i) / ξ ^ i) : ℝ)⌋ : ℝ) * (ξ ^ i) :=
begin
  by_cases hn : n =0,
  { rw [hn, range_zero, sum_empty, sub_eq_zero], refl },
  { replace hn : n ≥ 1 := le_of_not_gt ((not_iff_not.mpr nat.lt_one_iff).mpr hn),
    rw [← (nat.sub_add_cancel hn), finite_sum ξ x (n - 1)],
    simp only [sub_sub_cancel] at * },
end

variable [fact (0 < ξ)]

lemma exists_limit_y : ∃ a, tendsto (λ n, y ξ x n) at_top (𝓝 a) :=
begin
  have h_bdd : bdd_below (range (aux_y ξ x)),
  { use 0,
    intros z hz,
    obtain ⟨m, h_mz⟩ := (set.mem_range).mp hz,
    by_cases hm : m = 0,
    { simp_rw [hm, aux_y, if_pos] at h_mz,
      rw ← h_mz,
      exact eventually_pos_y ξ x 1 (le_of_eq (refl _)), },
      simp_rw [aux_y, (if_neg hm)] at h_mz,
      rw ← h_mz,
      replace hm : m ≥ 1 := le_of_not_gt ((not_iff_not.mpr nat.lt_one_iff).mpr hm),
      exact eventually_pos_y ξ x m hm },
  have := tendsto_at_top_cinfi (eventually_antitone ξ x) h_bdd,
  use (⨅ (i : ℕ), aux_y ξ x i),
  apply @tendsto.congr' _ _ (aux_y ξ x) _ _ _ _ this,
  apply (filter.eventually_eq_iff_exists_mem).mpr,
  use {n | n ≥ 1},
  simp only [mem_at_top_sets, ge_iff_le, mem_set_of_eq],
  use 1,
  simp only [imp_self, forall_const],
  intros n hn,
  replace hn : n ≥ 1 := by {simp only [*, ge_iff_le, mem_set_of_eq] at * },
  have := ne_of_lt (lt_of_lt_of_le nat.zero_lt_one hn),
  rw [aux_y, ite_eq_right_iff],
  tauto,
end

lemma summable_norm (r : ℝ≥0) (hr₁ : r < 1) :
      summable (λ i, ∥⌊(y ξ x i / ξ ^ i : ℝ)⌋∥ * (r ^ i)) :=
begin
  by_cases hr₀ : r = 0,
  { rw hr₀,
    apply @summable_of_ne_finset_zero _ _ _ _ _ (range 1),
    simp only [int.cast_eq_zero, nnreal.coe_zero, zero_pow_eq_zero, finset.mem_singleton,
      mul_eq_zero, range_one],
    intros _ hb,
    exact or.intro_right _ (nat.pos_of_ne_zero hb) },
  have h_nonneg : ∀ n : ℕ, n ≥ 1 → (r ^ n : ℝ) ≥ 0 := λ n _, pow_nonneg (r.2) n,
  have H : ∀ j : {i // i ∉ range 1}, j.1 ≥ 1,
  { rintro ⟨n, h_n⟩,
    simp only [ge_iff_le, finset.mem_singleton, range_one] at h_n,
    exact le_of_not_gt ((not_iff_not.mpr nat.lt_one_iff).mpr h_n) },
  apply (finset.summable_compl_iff (finset.range 1)).mp,
  swap, apply_instance,
  have h_nonneg : ∀ i : {i // i ∉ range 1}, (∥⌊(y ξ x i.1 / ξ ^ i.1 : ℝ)⌋∥) * r ^ i.1 ≥ 0,
    { intro i,
      apply mul_nonneg _ (h_nonneg i.1 (H i)),
      simp only [norm_nonneg] },
  obtain ⟨μ, hμ⟩  := bdd_floor ξ x,
  have h_bdd : ∀ i : {i // i ∉ range 1}, (∥⌊(y ξ x i.1 / ξ ^ i.1 : ℝ)⌋∥) ≤ μ,
  { rw upper_bounds at hμ,
    simp only [*, forall_apply_eq_imp_iff', lt_one_iff, set.mem_range, forall_const,
      forall_exists_index, nnreal.zero_le_coe, ge_iff_le, set.mem_set_of_eq, implies_true_iff,
      nonempty_of_inhabited, subtype.forall, pow_nonneg, finset.mem_range, subtype.val_eq_coe] at *,
    intros a ha,
    rw [finset.range_one, finset.mem_singleton] at ha,
    rw [subtype.coe_mk, int.norm_eq_abs],
    replace ha : a ≥ 1 := le_of_not_gt ((not_iff_not.mpr nat.lt_one_iff).mpr ha),
    rwa [abs_eq_self.mpr (eventually_pos_floor ξ x a ha)],
    exact hμ a },
  replace h_bdd : ∀ i : {i // i ∉ range 1}, (∥⌊(y ξ x i.1 / ξ ^ i.1 : ℝ)⌋∥) * r ^ i.1
      ≤ μ * r ^ i.1,
    { intro i,
    rw mul_le_mul_right,
    exacts [h_bdd i, pow_pos ((ne.symm hr₀).le_iff_lt.mp r.2) i.1] },
  apply summable_of_nonneg_of_le h_nonneg h_bdd,
  apply (@finset.summable_compl_iff _ _ _ _ _ (λ i, μ * r ^ i) (finset.range 1)).mpr,
  apply summable.mul_left,
  apply summable_geometric_of_abs_lt_1,
  rwa [← nnreal.val_eq_coe, abs_eq_self.mpr r.2],
end

lemma summable_floor (r : ℝ≥0) (hr₁ : r < 1) :
   summable (λ i, (⌊(y ξ x i / ξ ^ i : ℝ)⌋ : ℝ) * r ^ i) :=
begin
  have h_norm_eq : (λ i : ℕ, (∥⌊y ξ x i / ξ ^ i⌋∥ * (r ^ i : ℝ))) =
    (λ i : ℕ, (∥(⌊y ξ x i / ξ ^ i⌋ : ℝ) * (r ^ i)∥)),
    { funext,
      simp only [normed_field.norm_mul, nnreal.norm_eq, normed_field.norm_pow,
        mul_eq_mul_right_iff],
      rw [real.norm_eq_abs, int.norm_eq_abs],
      tauto },
  have := summable_norm ξ x r hr₁,
  rw h_norm_eq at this,
  apply summable_of_summable_norm (this),
end

lemma limit_y [fact (ξ < 1)]: tendsto (λ n, y ξ x n) at_top (𝓝 0) :=
begin
  have h_pos : 0 < ξ := fact.out _,
  let ξ₀ : ℝ≥0 := ⟨ξ, le_of_lt (fact.out _)⟩,
  have h_right : ∀ n, n ≥ 1 → (⌊(y ξ x n / ξ ^ n)⌋ : ℝ) ≤ (y ξ x n / ξ ^ n) :=
    (λ _ _, int.floor_le _),
  replace h_right : ∀ n, n ≥ 1 → (⌊(y ξ x n / ξ ^ n)⌋ : ℝ) * ξ ^ n  ≤ y ξ x n :=
    (λ n hn, (le_div_iff (pow_pos h_pos n)).mp (h_right n hn)),
  replace h_right : ∀ᶠ n in at_top, (⌊(y ξ x n / ξ ^ n)⌋ : ℝ) * ξ ^ n  ≤ y ξ x n,
  { simp only [ge_iff_le, eventually_at_top], use [1, h_right] },
  have h_left : ∀ n, n ≥ 1 → (y ξ x n / ξ ^ n) - 1 ≤ ⌊(y ξ x n / ξ ^ n)⌋ :=
    (λ n hn, le_of_lt (int.sub_one_lt_floor _)),
  replace h_left : ∀ n, n ≥ 1 → (y ξ x n - ξ ^ n) ≤ ⌊(y ξ x n / ξ ^ n)⌋ * ξ ^ n,
  { have h_one : ∀ n : ℕ, 0 < ξ ^ n := (λ n, pow_pos h_pos n),
    intros n hn,
    calc y ξ x n -  ξ ^ n = (y ξ x n * ξ ^ n / ξ ^ n  - ξ ^ n) :
                                                by {rw [mul_div_cancel _ (ne_of_lt (h_one n)).symm]}
                    ... = (y ξ x n / ξ ^ n * ξ ^ n  - ξ ^ n) :
                                                  by {rw [mul_div_assoc, ← div_mul_eq_mul_div_comm]}
                    ... = ((y ξ x n / ξ ^ n) - 1 ) * ξ ^ n :
                                            by {nth_rewrite_lhs 2 [← one_mul (ξ ^ n)], rw ← sub_mul}
                    ... ≤ ⌊(y ξ x n / ξ ^ n)⌋ * ξ ^ n :
                                                  (mul_le_mul_right (h_one n)).mpr (h_left n hn) },
  replace h_left : ∀ᶠ n in at_top, y ξ x n - ξ ^ n ≤ (⌊(y ξ x n / ξ ^ n)⌋ : ℝ) * ξ ^ n,
  { simp only [eventually_at_top], use [1, h_left] },
  have : tendsto (λ n, y ξ x n - ξ ^ n) at_top (𝓝 (exists_limit_y ξ x).some),
  { convert tendsto.add (exists_limit_y ξ x).some_spec (limit_neg_geometric ξ),
    rw add_zero } ,
  have h₁ := (le_of_tendsto_of_tendsto this
    (summable_floor ξ x ξ₀ _).tendsto_at_top_zero h_left).antisymm (le_of_tendsto_of_tendsto
    (summable_floor ξ x ξ₀ _).tendsto_at_top_zero (exists_limit_y ξ x).some_spec h_right),
  have := (exists_limit_y ξ x).some_spec,
  rwa h₁ at this,
  all_goals {rw [← nnreal.coe_lt_coe, nnreal.coe_one, subtype.coe_mk], exact fact.out _},
end

lemma has_sum_x [fact (ξ < 1)] : has_sum (λ i, (⌊(((y ξ x i) / ξ ^ i) : ℝ)⌋ : ℝ) * (ξ ^ i)) x :=
begin
  let ξ₀ : ℝ≥0 := ⟨ξ, le_of_lt (fact.out _)⟩,
  apply (summable_floor ξ x ξ₀ _).has_sum_iff_tendsto_nat.mpr,
  simp_rw [subtype.coe_mk, ← (finite_sum' ξ x), sub_eq_add_neg],
  nth_rewrite_rhs 0 [← add_zero x],
  apply @tendsto.const_add ℕ ℝ _ _ _ x 0 _ at_top,
  rw ← neg_zero,
  refine tendsto.neg (limit_y ξ x),
  { rw [← nnreal.coe_lt_coe, nnreal.coe_one, subtype.coe_mk],
    exact fact.out _},
end

end summability

section theta_surj

/--The map `θ` defined in Theorem 6.9 of Analytic.pdf. Given the definition of `tsum` we do not need to require that `r ≤ ξ` to simply define `θ`.-/
def θ (r : ℝ≥0) : (laurent_measures r (Fintype.of punit)) → ℝ :=
  λ F, tsum (λ n, (F.to_Rfct r n) * ξ ^ n)

theorem θ_surjective (x : ℝ) (r : ℝ≥0) [fact (r < 1)] [fact (0 < ξ)] [fact (ξ < 1)] :
  ∃ (F : laurent_measures r (Fintype.of punit)), (θ ξ r F) = x :=
begin
  let f₀ : ℤ → ℤ := λ m, int.rec_on m (λ i, ⌊((y ξ x i) / ξ ^ i)⌋) (0),
  let F₀ : Fintype.of punit → ℤ → ℤ := λ a, f₀,
  have hinj : function.injective (coe : ℕ → ℤ) := by {apply int.coe_nat_inj},
  have h_aux : ∀ n : ℤ, n ∉ set.range (coe : ℕ → ℤ) → f₀ n = 0,
  { rintro ( _ | _ ),
    simp only [forall_false_left, set.mem_range_self, not_true, int.of_nat_eq_coe],
    intro,
    refl },
  have h_range : ∀ n : ℤ,
    n ∉ set.range (coe : ℕ → ℤ) → (F₀ punit.star n : ℝ) * ξ ^ n = 0,
  swap,
  have h_range_norm : ∀ n : ℤ,
    n ∉ set.range (coe : ℕ → ℤ) → ∥F₀ punit.star n ∥ * r ^ n = 0, --sorry,
  swap,
  { have HF₀ : ∀ (s : Fintype.of punit), summable (λ (n : ℤ), ∥F₀ s n∥ * r ^ n),
    { intro s,
      apply (@function.injective.summable_iff _ _ _ _ _ _ _ hinj h_range_norm).mp,
      apply summable_norm ξ x r (fact.out _) },
    let F : laurent_measures r (Fintype.of punit) := ⟨F₀, HF₀⟩,
    use F,
    have : has_sum (λ n, ((F₀ punit.star n) : ℝ) * ξ ^ n) x,
    { apply (@function.injective.has_sum_iff _ _ _ _ _ _ x _ hinj h_range).mp,
      exact has_sum_x ξ x },
    apply has_sum.tsum_eq,
    exact this },
  all_goals { intros n hn,
    specialize h_aux n hn,
    simp only [h_aux, int.cast_eq_zero, mul_eq_zero, norm_eq_zero],
    tauto },
end

end theta_surj

section ker_theta
open submodule linear_map

variable (r : ℝ≥0)

lemma θ_is_linear : is_linear_map ℤ (θ ξ r) := sorry

def θ.to_linear : (laurent_measures r (Fintype.of punit)) →ₗ[ℤ] ℝ :=
{ to_fun := θ ξ r,
  map_add' := (θ_is_linear ξ r).1,
  map_smul' := (θ_is_linear ξ r).2 }

lemma harbater_15 [fact (0 < r)] [fact (r < 1)] [fact (0 < ξ)] [fact (ξ < (r : ℝ))] :
  ∃ f : (laurent_measures 1 (Fintype.of punit)),
    -- f = 1 + f: still need to add that f is congruent to 1 modulo T
    θ ξ 1 f  = 0 ∧ -- or θ ξ r f
    ∀ ζ : ℝ≥0, ζ ≤ r → (ζ : ℝ) ≠ ξ → θ ζ 1 f ≠ 0 :=
begin sorry,
end

lemma ker_θ_principal : submodule.is_principal (θ.to_linear ξ r).ker := sorry

def ker_generator : (laurent_measures r (Fintype.of punit)) :=
  @submodule.is_principal.generator _ _ _ _ _ (ker (θ.to_linear ξ r)) (ker_θ_principal ξ r)

/- [FAE] The following lemma needs that `(laurent_measures r (Fintype.of punit))` have a `mul`; but
I don't know if the lemma is actually needed -/
-- lemma ker_generator_non_zerodivisor : is_regular (ker_generator ξ) :=

end ker_theta

end theta
