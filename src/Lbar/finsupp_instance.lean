import Lbar.ses

open aux_thm69 finset finsupp
open_locale nnreal big_operators

noncomputable theory

universes u v

namespace laurent_measures
variables (r' : ℝ≥0) [fact (0 < r')] (S : Fintype)

/-- `Lker r' S` is the set of finite sums `F_s = ∑ a_{s,n}T^n ∈ ℤ[T⁻¹]`. -/
structure Lker (r' : ℝ≥0) (S : Fintype) :=
(to_fun      : S → ℕ → ℤ)
(exists_d    : ∃ d : ℕ, ∀ (s) {n}, d < n → to_fun s n = 0)

instance Lker_inhabited (r' : ℝ≥0) (S : Fintype) : inhabited (Lker r' S) :=
⟨{ to_fun := λ s, 0,
  exists_d := ⟨0, λ s n dn, rfl⟩ }⟩

/--  Any Laurent measure on `ℤ` restricts to a finite sum of negative indices.  -/
def Lbar_to_Lker [fact (r' < 1)] (F : laurent_measures r' S) :
  Lker r' S :=
{ to_fun := λ s n, F.to_fun s (- n),
  exists_d := begin
    obtain ⟨d, FF⟩ := exists_bdd_filtration _ _ F,
    refine ⟨(- d).to_nat, λ s n nd, FF _ _ _⟩,
    { exact neg_lt.mp ((-d).le_to_nat.trans_lt ((int.coe_nat_lt_coe_nat_iff _ _).mpr nd)) },
    { exact nnreal.coe_pos.mpr (fact.out _) },
    { exact (nnreal.coe_lt_coe.mpr (fact.out _)).trans_le nonneg.coe_one.le }
  end }

lemma finset.sum_summable {α M : Type*} [add_comm_group M] [topological_space M] (f : α →₀ M) :
  summable (λ a, f a) :=
summable_of_ne_finset_zero (λ b hb, not_mem_support_iff.mp hb)

def mymy (r' : ℝ≥0) (N : ℝ → ℝ≥0) (N0 : N 0 = 0) (N_neg : ∀ x, N (- x) = N x)
  (N_add : ∀ x y, N (x + y) ≤ N x + N y) : pseudo_normed_group (ℤ →₀ ℝ) :=
{ to_add_comm_group := finsupp.add_comm_group,
  filtration := λ c, {f | ∑' a : ℤ, N (f a) * r' ^ a ≤ c},
  filtration_mono := λ c d cd p ps, by { rw [set.mem_set_of_eq] at ⊢ ps, exact ps.trans cd },
  zero_mem_filtration := λ c, by simp only [N0, set.mem_set_of_eq, coe_zero, pi.zero_apply,
    zero_mul, tsum_zero, zero_le'],
  neg_mem_filtration := λ c x hx, by
    { simpa only [set.mem_set_of_eq, coe_neg, pi.neg_apply, N_neg] using hx },
  add_mem_filtration := λ c d x y, by {
    simp only [set.mem_set_of_eq, finsupp.coe_add, pi.add_apply],
    intros xc yd,
    refine le_trans _ (add_le_add xc yd),
    refine (tsum_le_tsum _ _ _).trans _,
    { exact λ z, (N (x z) + N (y z)) * r' ^ z },
    { intros b,
      exact mul_le_mul_of_nonneg_right (N_add _ _) zero_le' },
    { refine summable_of_ne_finset_zero (λ c (hc : c ∉ (x + y).support), _),
      rw [← pi.add_apply, ← finsupp.coe_add, not_mem_support_iff.mp hc, N0, zero_mul] },
    { refine summable_of_ne_finset_zero (λ c (hc : c ∉ x.support ∪ y.support), _),
      simp only [mem_union, mem_support_iff, ne.def] at hc,
      push_neg at hc,
      cases hc with hxc hyc,
      rw [hxc, hyc, N0, zero_add, zero_mul] },
    simp_rw add_mul,apply le_of_eq,
    refine tsum_add _ _,
    { refine summable_of_ne_finset_zero (λ c (hc : c ∉ x.support), _),
      simp only [mem_support_iff, not_not] at hc,
      simp [hc, N0] },
    { refine summable_of_ne_finset_zero (λ c (hc : c ∉ y.support), _),
      simp only [mem_support_iff, not_not] at hc,
      simp [hc, N0] } } }

#exit

instance (r' : ℝ≥0) (N : ℝ → ℝ≥0)
  (N0 : N 0 = 0) (N_neg : ∀ x, N (- x) = N x) (N_add : ∀ x y, N (x + y) ≤ N x + N y) :
  profinitely_filtered_pseudo_normed_group (finsupp ℤ ℝ) :=
{ topology := λ c, preorder.topology _,
  t2 := λ c, by {
    fconstructor,
    intros x y xy,
  },
  compact := sorry,
  continuous_add' := sorry,
  continuous_neg' := sorry,
  continuous_cast_le := sorry,
  td := sorry,
  ..(mymy r' N N0 N_neg N_add) }

#exit

instance {α : Type u} {M : Type v} [add_comm_group M]
  (μ : α → M → ℝ≥0) (negμ : ∀ a m, μ a (- m) = μ a m)
  (addμ : ∀ a m n, μ a (m + n) = μ a m + μ a n) :
  profinitely_filtered_pseudo_normed_group (finsupp α M) :=
{ to_add_comm_group := finsupp.add_comm_group,
  filtration := λ r, {f | f.sum μ ≤ r},
  filtration_mono := λ c d cd p ps, by { rw [set.mem_set_of_eq] at ⊢ ps, exact ps.trans cd },
  zero_mem_filtration := λ c, by simp,
  neg_mem_filtration := λ c x hx, by
    simpa only [finsupp.sum, negμ, set.mem_set_of_eq, support_neg, coe_neg, pi.neg_apply] using hx,
  add_mem_filtration := λ c d x y, by {
    classical,
    simp only [set.mem_set_of_eq, finsupp.coe_add, pi.add_apply],
    intros xs ys,
    refine le_trans _ (add_le_add xs ys),
    have : (x + y).support ⊆ _ := support_add,
    simp only [finsupp.sum, finsupp.coe_add, pi.add_apply, addμ],
    transitivity (x + y).support.sum (λ (x_1 : α), μ x_1 (x x_1)) +
      (x + y).support.sum (λ (x_1 : α), μ x_1 (y x_1)),
      sorry,
    refine add_le_add _ _,
    have : (x + y).support = x.support ∪ (y.support \ x.support),
    apply le_antisymm,
    simpa,
    intros a ha,
    cases mem_union.mp ha with hh hh,
    apply mem_support_iff.mpr,
    simp,
    apply
    apply le_of_eq,

    --have : ∀ a : (x + y).support,
    apply support_subset_iff,
    transitivity x.sum μ + (x + y).sum μ,
    rw ← finsupp.sum_add_,
--    simp [finsupp.sum, addμ, support_add],
    transitivity (x + y).support.sum (λ (a : α), μ a (x a)) + (x + y).support.sum (λ (b : α), μ b (y b)),
--    library_search,
    transitivity x.support.sum (λ (a : α), μ a (x a) + μ a (y a)) + y.support.sum (λ (b : α), μ b (x b) + μ b (y b)),

    --library_search,
    rw finsupp.add,
    refine sum_le_sum_of_subset_of_nonneg (support_add : (x + y).support ⊆ _) _,
  },
  topology := _,
  t2 := _,
  compact := _,
  continuous_add' := _,
  continuous_neg' := _,
  continuous_cast_le := _,
  td := _ }


variables [fact (r' < 1)]



end laurent_measures

#exit
import data.real.nnreal
import analysis.normed_space.basic

open_locale nnreal classical

lemma int.nnnorm_eq_nat_abs (n : ℤ) : ∥n∥₊ = n.nat_abs :=
(nnreal.coe_nat_abs n).symm
