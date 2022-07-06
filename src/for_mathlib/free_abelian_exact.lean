import analysis.normed.group.basic
import topology.algebra.infinite_sum
import for_mathlib.AddCommGroup.exact
import for_mathlib.free_abelian_group2

noncomputable theory

open category_theory
open_locale big_operators

variables (A : Type*) [add_comm_group A]

namespace free_abelian_group

def σπ : free_abelian_group (A × A) →+ free_abelian_group A :=
free_abelian_group.map prod.fst + free_abelian_group.map prod.snd -
free_abelian_group.map (function.uncurry (+))

lemma σπ_of (x) : σπ A (of x) = (of x.1) + (of x.2) - of (x.1 + x.2) :=
by simp only [σπ, add_monoid_hom.sub_apply, add_monoid_hom.add_apply, map_of_apply, function.uncurry]

lemma σπ_comp_zero : AddCommGroup.of_hom (σπ A) ≫ AddCommGroup.of_hom (lift id) = 0 :=
begin
  ext ⟨x,y⟩,
  simp only [comp_apply, AddCommGroup.of_hom_apply, σπ_of, _root_.map_sub, _root_.map_add,
    lift.of, id.def, sub_self, AddCommGroup.zero_apply],
end

section norm

open_locale nnreal

variables {X : Type*} (a b : free_abelian_group X)

def norm : ℕ := ∑ x in a.support, (coeff x a).nat_abs

lemma tsum_norm : (a.norm : ℝ) = ∑' x, |((coeff x a) : ℝ)| :=
begin
  rw [@tsum_eq_sum _ _ _ _ _ (λ x : X, |((coeff x a) : ℝ)|) a.support _, norm, nat.cast_sum],
  apply finset.sum_congr (refl a.support),
  { exact (λ x _, (int.cast_nat_abs _))} ,
  { intros x hx,
    rw [abs_eq_zero, int.cast_eq_zero],
    exact (not_mem_support_iff x a).mp hx },
end

lemma summable_tsum_norm : summable (λ x, |((coeff x a) : ℝ)|) :=
begin
  apply summable_of_ne_finset_zero,
  { intros x hx,
    rw [abs_eq_zero, int.cast_eq_zero],
    exact (not_mem_support_iff x a).mp hx },
end

@[simp] lemma norm_of (x : X) : (of x).norm = 1 := by {simp only [norm, support_of,
  finset.sum_singleton, coeff_of_self, int.nat_abs_one]}

lemma norm_add : (a + b).norm ≤ a.norm + b.norm :=
begin
  rw [← @nat.cast_le ℝ _ _, tsum_norm, nat.cast_add, tsum_norm, tsum_norm, ← tsum_add
    (summable_tsum_norm a) (summable_tsum_norm b)],
  refine tsum_le_tsum _
    (summable_tsum_norm (a + b) ) (summable.add (summable_tsum_norm _) (summable_tsum_norm _)),
  intro,
  rw [_root_.map_add, int.cast_add],
  exact abs_add _ _ ,
end

@[simp] lemma norm_neg : (-a).norm = a.norm :=
begin
  apply_fun (coe : ℕ → ℝ),
  { rw [tsum_norm, tsum_norm, tsum_congr],
    intro x,
    rw [_root_.map_neg, int.cast_neg, abs_neg] },
  exact nat.cast_injective,
end

lemma norm_sub : (a - b).norm ≤ a.norm + b.norm := by {rw [sub_eq_add_neg, ← norm_neg b],
  exact norm_add _ _}

@[simp] lemma norm_eq_zero_iff : a.norm = 0 ↔ a = 0 :=
begin
  split,
  { intro h,
    rw [← @nat.cast_eq_zero ℝ _ _ _ _, tsum_norm] at h,
    have H := (has_sum_zero_iff_of_nonneg _).mp (((summable_tsum_norm a).has_sum_iff).mpr h),
    have h_cz : ∀ x : X, coeff x a = 0,
    { intro x,
      have := (function.funext_iff).mp H x,
      simp only [pi.zero_apply, abs_eq_zero, int.cast_eq_zero] at this,
      exact this },
    apply_fun to_finsupp,
    ext,
    exacts [h_cz _, add_equiv.injective (equiv_finsupp X), (λ _, abs_nonneg _)] },
  { intro h,
    have h_cz : ∀ x : X, coeff x a = 0,
    { intro x,
      rw h,
      simp only [_root_.map_zero, eq_self_iff_true] },
    apply finset.sum_eq_zero,
    rintros x -,
    exact (int.nat_abs_eq_zero.mpr (h_cz x))}
end

lemma exists_of_norm_eq_succ_aux1 (n : ℤ) (H : 0 < n) :
  n.nat_abs = (n - 1).nat_abs + 1 :=
begin
  rcases n with ((_|n)|n),
  { exfalso, revert H, dec_trivial },
  { suffices : int.of_nat n.succ - 1 = int.of_nat n, { rw this, refl, },
    simp only [int.of_nat_eq_coe, int.coe_nat_succ, add_tsub_cancel_right], },
  { exfalso, revert H, dec_trivial },
end

lemma exists_of_norm_eq_succ_aux2 (n : ℤ) (H : n < 0) :
  n.nat_abs = (n + 1).nat_abs + 1 :=
begin
  rw [← right.neg_pos_iff] at H,
  simpa only [int.nat_abs_neg, sub_eq_add_neg, ← neg_add] using
    exists_of_norm_eq_succ_aux1 (-n) H,
end

lemma exists_of_norm_eq_succ (n : ℕ) (han : a.norm = n.succ) :
  ∃ b x, (a = b + of x ∨ a = b - of x) ∧ b.norm = n :=
begin
  have aux : a.norm ≠ 0, { rw han, dec_trivial },
  dsimp [norm] at aux,
  erw not_iff_not.mpr finset.sum_eq_zero_iff at aux, push_neg at aux,
  rcases aux with ⟨x, hxa, ha⟩,
  rcases lt_trichotomy (coeff x a) 0 with (H|H|H), rotate,
  { apply_fun int.nat_abs at H, contradiction },
  { refine ⟨a - of x, x, or.inl (sub_add_cancel _ _).symm, _⟩,
    apply nat.succ_injective, rw [← han], symmetry,
    dsimp only [norm, nat.succ_eq_add_one],
    classical,
    have : (a - of x).support ⊆ a.support,
    { rw [sub_eq_add_neg], refine (support_add _ _).trans _,
      simp only [support_neg, support_of, finset.union_subset_iff, finset.subset.refl,
        finset.singleton_subset_iff, true_and, hxa], },
    rw [finset.sum_subset this],
    swap, { intros y hy1 hy2, rwa [int.nat_abs_eq_zero, ← not_mem_support_iff] },
    rw [← finset.insert_erase hxa, finset.sum_insert (finset.not_mem_erase _ _),
      finset.sum_insert (finset.not_mem_erase _ _), add_right_comm],
    simp only [_root_.map_sub], congr' 1,
    { rw [coeff_of_self], apply exists_of_norm_eq_succ_aux1 _ H },
    { refine finset.sum_congr rfl _, intros y hy, rw [coeff_of_not_mem_support (of x), sub_zero],
      simp only [finset.mem_erase, ne.def] at hy,
      simpa only [support_of, finset.mem_singleton] using hy.1, } },
  { refine ⟨a + of x, x, or.inr (add_sub_cancel _ _).symm, _⟩,
    apply nat.succ_injective, rw [← han], symmetry,
    dsimp only [norm, nat.succ_eq_add_one],
    classical,
    have : (a + of x).support ⊆ a.support,
    { refine (support_add _ _).trans _,
      simp only [support_neg, support_of, finset.union_subset_iff, finset.subset.refl,
        finset.singleton_subset_iff, true_and, hxa], },
    rw [finset.sum_subset this],
    swap, { intros y hy1 hy2, rwa [int.nat_abs_eq_zero, ← not_mem_support_iff] },
    rw [← finset.insert_erase hxa, finset.sum_insert (finset.not_mem_erase _ _),
      finset.sum_insert (finset.not_mem_erase _ _), add_right_comm],
    simp only [_root_.map_add], congr' 1,
    { rw [coeff_of_self], apply exists_of_norm_eq_succ_aux2 _ H },
    { refine finset.sum_congr rfl _, intros y hy, rw [coeff_of_not_mem_support (of x), add_zero],
      simp only [finset.mem_erase, ne.def] at hy,
      simpa only [support_of, finset.mem_singleton] using hy.1, } },
end

-- SELFCONTAINED
lemma norm_eq_one_iff : a.norm = 1 ↔ ∃ x, a = of x ∨ a = -of x :=
sorry

end norm

lemma σπ_of_00 : σπ A (of (0,0)) = of 0 :=
by simp only [σπ_of, add_zero, add_sub_cancel']

lemma exact_σπ_induction (a : free_abelian_group A) (ha : free_abelian_group.lift id a = 0)
  (n : ℕ) (hn : a.norm ≤ n) :
  ∃ x, free_abelian_group.σπ A x = a :=
begin
  induction n with n ih generalizing a,
  { simp only [nat.le_zero_iff, norm_eq_zero_iff] at hn, subst a, exact ⟨0, _root_.map_zero _⟩ },
  erw [nat.le_add_one_iff] at hn, cases hn with hn hn, { exact ih a ha hn },
  cases n,
  { rw [norm_eq_one_iff] at hn, rcases hn with ⟨a, (rfl|rfl)⟩,
    all_goals { simp only [lift.of, _root_.map_neg, _root_.id, neg_eq_zero] at ha, subst a, },
    { exact ⟨of (0,0), σπ_of_00 _⟩ },
    { refine ⟨-of (0,0), _⟩, rw [_root_.map_neg, σπ_of_00] } },
  obtain ⟨b, y, H1, hbn⟩ := exists_of_norm_eq_succ _ _ hn,
  obtain ⟨c, x, H2, hcn⟩ := exists_of_norm_eq_succ _ _ hbn,
  rcases H1 with (rfl|rfl); rcases H2 with (rfl|rfl),
  { obtain ⟨p, hp⟩ := ih (c + of (x+y)) _ _, rotate,
    { simpa only [lift.of, _root_.map_add, id.def, add_assoc] using ha, },
    { refine (norm_add _ _).trans _, rw [hcn, norm_of], },
    refine ⟨p + of (x,y), _⟩,
    simp only [_root_.map_add, hp, σπ_of, add_assoc, add_right_inj],
    rw [add_comm (of (x+y)), sub_add_cancel], },
  { obtain ⟨p, hp⟩ := ih (c + of (y-x)) _ _, rotate,
    { simpa only [lift.of, _root_.map_add, _root_.map_neg, id.def,
        add_assoc, sub_eq_add_neg, add_comm y] using ha, },
    { refine (norm_add _ _).trans _, rw [hcn, norm_of], },
    refine ⟨p - of (y-x,x), _⟩,
    simp only [_root_.map_add, _root_.map_neg, sub_eq_add_neg, hp, σπ_of,
      neg_add_cancel_right, neg_add_rev, neg_neg, add_assoc,
      add_left_neg, add_zero, add_right_inj],
    rw [add_comm (of (y+-x)), add_comm _ (of y)],
    simp only [add_assoc, add_left_neg, add_zero], },
  { obtain ⟨p, hp⟩ := ih (c + of (x-y)) _ _, rotate,
    { simpa only [lift.of, _root_.map_add, _root_.map_neg, id.def,
        add_assoc, sub_eq_add_neg] using ha, },
    { refine (norm_add _ _).trans _, rw [hcn, norm_of], },
    refine ⟨p - of (x-y,y), _⟩,
    simp only [_root_.map_add, _root_.map_neg, sub_eq_add_neg, hp, σπ_of,
      neg_add_cancel_right, neg_add_rev, neg_neg, add_assoc, add_right_inj,
      add_left_neg, add_zero],
    rw [add_comm (of (x+-y))],
    simp only [add_assoc, add_left_neg, add_zero], },
  { obtain ⟨p, hp⟩ := ih (c - of (x+y)) _ _, rotate,
    { simpa only [lift.of, _root_.map_add, _root_.map_neg, id.def, neg_add,
        add_assoc, sub_eq_add_neg] using ha, },
    { refine (norm_sub _ _).trans _, rw [hcn, norm_of], },
    refine ⟨p - of (x,y), _⟩,
    simp only [_root_.map_add, _root_.map_neg, sub_eq_add_neg, hp, σπ_of,
      neg_add_cancel_right, neg_add_rev, neg_neg, add_assoc, neg_add_cancel_left],
    rw add_comm (-of x) },
end

lemma exact_σπ : exact
  (AddCommGroup.of_hom $ free_abelian_group.σπ A)
  (AddCommGroup.of_hom $ free_abelian_group.lift id) :=
begin
  rw AddCommGroup.exact_iff',
  refine ⟨σπ_comp_zero _, _⟩,
  intros a ha,
  obtain ⟨p, hp⟩ := exact_σπ_induction A a ha a.norm le_rfl,
  exact ⟨p, hp⟩
end

end free_abelian_group
