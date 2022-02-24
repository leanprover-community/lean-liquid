import Lbar.ses

open aux_thm69 finset finsupp laurent_measures
open_locale nnreal big_operators

noncomputable theory

universes u v

section families_of_add_comm_groups

variables (S A : Type*) [add_comm_group A]

-- by apply_instance works, but having this instance explicitly, allows
-- `finsupp_add_group` to work.
instance add_comm_group_finsupp {α β γ : Type*} [add_comm_group γ] : add_comm_group (α → β →₀ γ) :=
pi.add_comm_group

--  I had some trouble getting Lean to accept this instance, without the explicit instance
--  `add_comm_group_finsupp`
instance finsupp_add_group : add_comm_group (S → ℤ →₀ ℝ) := by apply_instance -- works

/--  A function from a `Fintype` is automatically a `finsupp`, when the target has a zero. -/
def finsupp_of_fintype_domain {α : Type*} [has_zero α] {S : Fintype} (F : S → α) : S →₀ α :=
{ support            := (set.finite.of_fintype {s | F s ≠ 0}).to_finset,
  to_fun             := F,
  mem_support_to_fun := by simp }

instance fintype.sum_nnnorm {S : Fintype} {α : Type*} [has_nnnorm α] : has_nnnorm (S → α) :=
{ nnnorm := λ F, ∑ s, ∥F s∥₊ }

lemma finset.sum_add {α β : Type*} [add_comm_monoid β] {F G : α → β} (s : finset α) :
  ∑ x in s, (F x + G x) = ∑ x in s, F x + ∑ x in s, G x :=
begin
  classical,
  refine finset.induction_on s (by simp) _,
  intros a s as h,
  rw [sum_insert as, sum_insert as, sum_insert as, h],
  abel,
end

instance sum_nnnorm (S : Fintype) (α : Type*) [has_zero α] [has_nnnorm α] :
  has_nnnorm (S → α) :=
{ nnnorm := λ F, ∑ b, ∥F b∥₊ }

@[simp]
lemma sum_nnnorm_def {S : Fintype} {α : Type*} [has_zero α] [has_nnnorm α] (F : S → α) :
  ∥F∥₊ = ∑ b, ∥F b∥₊ := rfl

lemma sum_nnnorm_add_le {S : Fintype} {β : Type*} [semi_normed_group β]
  (F G : S → β) :
  ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  simp only [sum_nnnorm_def, pi.add_apply],
  exact le_trans (sum_le_sum (λ i hi, nnnorm_add_le _ _)) (finset.sum_add _).le,
end

/-  Johan's version.
@[nolint unused_arguments]
def some_nice_name (r : ℝ≥0) (S : Fintype) := S → polynomial ℤ
-/

@[nolint unused_arguments, derive add_comm_group]
def some_nice_name (r : ℝ≥0) (S : Fintype) := S → (ℤ →₀ ℝ)

namespace some_nice_name

--instance (r : ℝ≥0) (S : Fintype) : has_nnnorm (some_nice_name r S) :=
--@sum_nnnorm S (ℤ →₀ ℝ) _ (⟨λ F, ∑' x, ∥F x∥₊ * r ^ x⟩)

instance (r : ℝ≥0) (S : Fintype) : has_nnnorm (some_nice_name r S) :=
@sum_nnnorm S (ℤ →₀ ℝ) _ (⟨λ F, ∑ x in F.support, ∥F x∥₊ * r ^ x⟩)

@[simp]
lemma nnnorm_zero {r : ℝ≥0} {S : Fintype} : ∥(0 : some_nice_name r S)∥₊ = 0 :=
by simp only [sum_nnnorm_def, pi.zero_apply, coe_zero, nnnorm_zero, zero_mul, tsum_zero,
  sum_const_zero]

@[simp]
lemma nnnorm_neg {r : ℝ≥0} {S : Fintype} (F : some_nice_name r S) :
  ∥-F∥₊ = ∥F∥₊ :=
by simp only [_root_.nnnorm_neg, sum_nnnorm_def, pi.neg_apply, coe_neg, support_neg]

lemma nnnorm_sub {r : ℝ≥0} {S : Fintype} (F G : some_nice_name r S) :
  ∥F - G∥₊ = ∥G - F∥₊ :=
by rw [← nnnorm_neg (F - G), neg_sub]

instance {r : ℝ≥0} {S : Fintype} : topological_space (some_nice_name r S) :=
by simpa only [some_nice_name] using preorder.topology (↥S → ℤ →₀ ℝ)

--instance : topological_space (ℤ →₀ ℝ) :=
--preorder.topology (ℤ →₀ ℝ)

--instance {r : ℝ≥0} {S : Fintype} : has_continuous_add (ℤ →₀ ℝ) :=
--{ continuous_add := by {
--sorry;  dunfold some_nice_name;
--  sorry
--} }

--instance {r : ℝ≥0} {S : Fintype} : has_continuous_add (some_nice_name r S) :=
--{ continuous_add := by {
--  dunfold some_nice_name,
--  sorry
--} }

lemma qui {l : ℤ →₀ ℝ} {s : finset ℤ} (ls : l.support ⊆ s) :
  ∑ a in l.support, l a = ∑ a in s, l a :=
sum_subset ls (by simp only [mem_support_iff, not_not, imp_self, implies_true_iff])

open_locale classical
lemma add_zero_dists {α β : Type*} [add_group β]
  (x y z : α →₀ β) (l : α) (h : x l + y l + z l = 0)
  (hl : l ∈ x.support) :
  l ∈ y.support ∪ z.support :=
begin
  contrapose hl,
  simp only [mem_support_iff, coe_sub, pi.sub_apply, ne.def, not_not, mem_union] at hl ⊢,
  push_neg at hl,
  cases hl with h1 h2,
  rwa [h1, h2, add_zero, add_zero] at h,
end

lemma dists {α β : Type*} [add_group β]
  (x y z : α →₀ β) (l : α)
  (hl : l ∈ (x - z).support) :
  l ∈ (x - y).support ∪ (y - z).support :=
begin
  have : l ∈ (- (x - z)).support,rwa support_neg,
  refine add_zero_dists _ _ _ _ _ this,
  simp only [neg_sub, coe_sub, pi.sub_apply, sub_add_sub_cancel, sub_self]
end

instance {r : ℝ≥0} {S : Fintype} : semi_normed_group (some_nice_name r S) :=
{ norm := λ F, ∥F∥₊,
  dist := λ F G, ∥F - G∥₊,
  dist_self := λ F, by simp only [sub_self, nnnorm_zero, nonneg.coe_zero],
  dist_comm := λ F G, by simp only [dist, nnnorm_sub],
  dist_triangle := λ x y z, by {simp only [sum_nnnorm_def, pi.sub_apply, coe_sub],
  norm_cast,
  rw ← finset.sum_add,
  apply sum_le_sum,
  intros i hi,
--  have xy : (x i - y i).support ⊆ (x i - y i).support ∪ (y i - z i).support :=
--    subset_union_left _ _,
--  have yz : (y i - z i).support ⊆ (x i - y i).support ∪ (y i - z i).support :=
--    subset_union_right _ _,

  rw sum_subset (subset_union_left _ _ : _ ⊆ (x i - y i).support ∪ (y i - z i).support),
  rw sum_subset (subset_union_right _ _ : _ ⊆ (x i - y i).support ∪ (y i - z i).support),
  rw sum_subset (_ : _ ⊆ (x i - y i).support ∪ (y i - z i).support),
  rw ← finset.sum_add,
  apply sum_le_sum,
  intros j hj,
  rw ← add_mul,
  refine mul_le_mul_of_nonneg_right _ (zero_le _),
  apply nnreal.coe_le_coe.mp,
  exact dist_triangle ((x i) j) _ _,
  intros k hk hh,
  simp only [mem_support_iff, coe_sub, pi.sub_apply, not_not] at hh,
  convert zero_mul _,
  simp only [hh, nnnorm_eq_zero],
  intros l hl,
  extract_goal,
--  simp [hh],
   },
--  edist := _,
  edist_dist := _,
--  to_uniform_space := _,
  uniformity_dist := _,
  dist_eq := _,
  ..(infer_instance : add_comm_group _) }

instance mymy (S : Fintype) (r : ℝ≥0) : pseudo_normed_group (some_nice_name r S) :=
{ to_add_comm_group := finsupp_add_group S,
  filtration := λ c, {F : some_nice_name r S | ∥F∥₊ ≤ c},
  filtration_mono := λ c d cd x hx, by { rw set.mem_set_of_eq at hx ⊢, exact hx.trans cd },
  zero_mem_filtration := λ c,
    by { simp only [set.mem_set_of_eq, nnnorm_zero, zero_le'] },
  neg_mem_filtration := λ c F hF,
    by simpa only [sum_nnnorm_def, set.mem_set_of_eq, pi.neg_apply, coe_neg, _root_.nnnorm_neg],
  add_mem_filtration := λ c d F G hF hG,
    by {
      simp only [sum_nnnorm_def, set.mem_set_of_eq, pi.add_apply, finsupp.coe_add],
      refine le_trans _ (add_le_add hF hG),
      apply sum_nnnorm_add_le F G,
      --exact (sum_nnnorm_add_le F G).trans (add_le_add hF hG),
      --simpa using (sum_nnnorm_add_le F G).trans (add_le_add hF hG)},
     } }

end some_nice_name

#exit
instance (r : ℝ≥0) (S : Fintype) : pseudo_normed_group (some_nice_name r S) :=
{ to_add_comm_group := by { convert finsupp_add_group S,},
  filtration := _,
  filtration_mono := _,
  zero_mem_filtration := _,
  neg_mem_filtration := _,
  add_mem_filtration := _ }

--structure with_r (r' : ℝ≥0) :=
--(ℤ →₀ ℝ)
instance mymy (S : Fintype) (r' : ℝ≥0) : pseudo_normed_group (S → ℤ →₀ ℝ) :=
{ to_add_comm_group := finsupp_add_group S,
  filtration := λ c, by {
    letI Q : has_nnnorm (S → (ℤ →₀ ℝ)) := @sum_nnnorm S (ℤ →₀ ℝ) _ (by
      refine ⟨λ F, ∑' x, ∥F x∥₊ * r' ^ x⟩),
    exact {F | ∥F∥₊ ≤ c}},
  filtration_mono := λ c d cd x hx, by { rw set.mem_set_of_eq at hx ⊢, exact hx.trans cd },
  zero_mem_filtration := λ c,
    by simp only [nnnorm, set.mem_set_of_eq, support_zero, sum_empty, zero_le'],
  neg_mem_filtration := λ c F hF,
    by simpa only [set.mem_set_of_eq, nnnorm, norm_neg, support_neg, coe_neg, pi.neg_apply],
  add_mem_filtration := λ c d F G hF hG,
    by simpa using (sum_nnnorm_add_le F G).trans (add_le_add hF hG) }

namespace works_but_not_what_I_want

instance sum_nnnorm {α β : Type*} [has_zero α] [has_nnnorm α] : has_nnnorm (β →₀ α) :=
{ nnnorm := λ F, ∑ b in F.support, ∥F b∥₊ }

lemma sum_nnnorm_add_le {α β : Type*} [semi_normed_group β]
--[ordered_add_comm_monoid β]
-- [has_nnnorm β]
  (F G : α →₀ β) :
  ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  classical,
  simp only [nnnorm, finsupp.coe_add, pi.add_apply],
  refine le_trans (sum_le_sum_of_subset support_add) _,
  refine le_trans (sum_le_sum (λ i hi, nnnorm_add_le _ _)) (le_of_eq _),
  refine (F.support ∪ G.support).sum_add.trans _,
  conv in (∑ x in _, ∥G x∥₊) { congr, rw union_comm },
  congr' 1;
  { rw [← union_sdiff_self_eq_union, sum_union disjoint_sdiff],
    convert add_zero _,
    simp only [sum_eq_zero_iff, mem_sdiff, mem_support_iff, ne.def, not_not, and_imp],
    exact λ _ _ h, by simp only [h, nnnorm_zero] }
end

instance mymy (r' : ℝ≥0) : pseudo_normed_group (ℤ →₀ ℝ) :=
{ to_add_comm_group := finsupp.add_comm_group,
  filtration := λ c, {F | ∥F∥₊ ≤ c},
  filtration_mono := λ c d cd x hx, by { rw set.mem_set_of_eq at hx ⊢, exact hx.trans cd },
  zero_mem_filtration := λ c,
    by simp only [nnnorm, set.mem_set_of_eq, support_zero, sum_empty, zero_le'],
  neg_mem_filtration := λ c F hF,
    by simpa only [set.mem_set_of_eq, nnnorm, norm_neg, support_neg, coe_neg, pi.neg_apply],
  add_mem_filtration := λ c d F G hF hG,
    by simpa using (sum_nnnorm_add_le F G).trans (add_le_add hF hG) }

end works_but_not_what_I_want

end families_of_add_comm_groups

namespace flaurent
section add_group_instance

end add_group_instance
/-
/-- Addition in `S → (ℤ →₀ ℝ)`, defined as pointwise addition. -/
def add (F : S → (ℤ →₀ ℝ)) (G : S → (ℤ →₀ ℝ)) : S → (ℤ →₀ ℝ) :=
λ s, F s + G s

/-- Subtraction in `S → (ℤ →₀ ℝ)`, defined as pointwise subtraction. -/
def sub (F : S → (ℤ →₀ ℝ)) (G : S → (ℤ →₀ ℝ)) : S → (ℤ →₀ ℝ) :=
λ s, F s - G s

/-- Negation in `S → (ℤ →₀ ℝ)`, defined as pointwise negation. -/
def neg (F : S → (ℤ →₀ ℝ)) : S → (ℤ →₀ ℝ) :=
λ s, - F s

--instance : has_zero (S → (ℤ →₀ ℝ)) := by apply_instance
instance : has_add (S → (ℤ →₀ ℝ)) := ⟨add⟩
instance : has_sub (S → (ℤ →₀ ℝ)) := ⟨sub⟩
instance : has_neg (S → (ℤ →₀ ℝ)) := ⟨neg⟩

instance : inhabited (S → (ℤ →₀ ℝ)) := ⟨0⟩

/-- Tailored scalar multiplication by natural numbers. -/
protected def nsmul (N : ℕ) (F : S → (ℤ →₀ ℝ)) : S → (ℤ →₀ ℝ) :=
λ s, N • F s

/-- Tailored scalar multiplication by integers. -/
protected def zsmul (N : ℤ) (F : S → (ℤ →₀ ℝ)) : S → (ℤ →₀ ℝ) :=
λ s, N • F s
-/



variables (r' : ℝ≥0) (S : Fintype)
def my_nnnorm {α β : Type*} [has_zero β] [has_nnnorm β] (ρ : ℝ≥0) (ex : α → ℤ) (F : α →₀ β) : ℝ≥0 :=
∑' n, ∥F n∥₊ * ρ ^ ex n

/-- The norm of `F : S → (ℤ →₀ ℝ)` as nonnegative real number.
It is defined as `∑ s, ∑' n, (↑(F s n).nat_abs * r' ^ n)`. -/
protected def nnnorm (F : S → (ℤ →₀ ℝ)) : ℝ≥0 :=
my_nnnorm r' id (finsupp_of_fintype_domain F)

/-- The norm of `F : S → (ℤ →₀ ℝ)` as nonnegative real number.
It is defined as `∑ s, ∑' n, (↑(F s n).nat_abs * r' ^ n)`. -/
protected def nnnorm (F : S → (ℤ →₀ ℝ)) : ℝ≥0 :=
∑ s, ∑' n, ∥F s n∥₊ * r' ^ n

/-- `Lfin S` is the set of finite sums `F_s = ∑ a_{s,n}T^n ∈ Tℤ[[T]]`. -/
structure Lfin (S : Fintype) :=
(to_fun : S → ℤ →₀ ℤ)
(r'     : ℝ≥0)

instance pro : inhabited (Lfin S) :=
⟨{ to_fun := 0, r' := 0 }⟩

local notation `ℒ₀ `:1000 S := flaurent.Lfin S

instance : has_nnnorm ℒ₀ S :=
⟨λ F, flaurent.nnnorm F.r' S (λ s, ⟨(F.to_fun s).support, coe ∘ (F.to_fun s), by simp⟩)⟩


variable [fact (0 < r')]

/-- `flaurent r' S` is the set of finite sums `F_s = ∑ a_{s,n}T^n ∈ ℤ[T⁻¹]`. -/
local notation `ℒ₀` := (S → (ℤ →₀ ℝ))

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

/-
def mymy (r' : ℝ≥0) (S : Fintype) : pseudo_normed_group (S → (ℤ →₀ ℝ)) :=
{ filtration := λ c, {F | ∥F∥₊ ≤ c},
  filtration_mono := λ c₁ c₂ h F hF, le_trans hF h,
  zero_mem_filtration := λ c, by { dsimp, rw nnnorm_zero, apply zero_le' },
  neg_mem_filtration := λ c F hF, by { dsimp, rwa nnnorm_neg },
  add_mem_filtration := λ c₁ c₂ F₁ F₂ hF₁ hF₂,
  by exact le_trans (nnnorm_add_le _ _) (add_le_add hF₁ hF₂) }
-/


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

end flaurent
/-
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
-/
