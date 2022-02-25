import pseudo_normed_group.basic
import category_theory.Fintype
import analysis.normed_space.basic

open finset finsupp
open_locale nnreal big_operators

noncomputable theory

universes u v

section families_of_add_comm_groups

lemma finset.sum_add {α β : Type*} [add_comm_monoid β] {F G : α → β} (s : finset α) :
  ∑ x in s, (F x + G x) = ∑ x in s, F x + ∑ x in s, G x :=
begin
  classical,
  refine finset.induction_on s (by simp) (λ a s as h, _),
  rw [sum_insert as, sum_insert as, sum_insert as, h],
  abel,
end

variables {S : Fintype} {α : Type*}

instance sum_nnnorm [has_nnnorm α] : has_nnnorm (S → α) :=
{ nnnorm := λ F, ∑ b, ∥F b∥₊ }

@[simp]
lemma sum_nnnorm_def [has_nnnorm α] (F : S → α) : ∥F∥₊ = ∑ b, ∥F b∥₊ := rfl

lemma sum_nnnorm_add_le [semi_normed_group α] (F G : S → α) :
  ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
show ∑ s, ∥F s + G s∥₊ ≤ ∑ s, ∥F s∥₊ + ∑ s, ∥G s∥₊, from
le_trans (sum_le_sum (λ i hi, nnnorm_add_le _ _)) univ.sum_add.le

end families_of_add_comm_groups

lemma add_zero_dists {α β : Type*} [decidable_eq α] [add_zero_class β] {l : α} {x y z : α →₀ β}
  (h : x l + y l + z l = 0) (hl : l ∈ x.support) :
  l ∈ y.support ∪ z.support :=
begin
  simp only [mem_support_iff, ne.def, mem_union] at hl ⊢,
  contrapose! hl,
  simpa only [hl, add_zero] using h,
end

lemma dists {α β : Type*} [decidable_eq α] [add_group β] {l : α} {x y z : α →₀ β}
  (hl : l ∈ (x - z).support) :
  l ∈ (x - y).support ∪ (y - z).support :=
have xz : l ∈ (- (x - z)).support, by rwa support_neg,
add_zero_dists (by simp only [neg_sub, coe_sub, pi.sub_apply, sub_add_sub_cancel, sub_self]) xz

/--  Let `r : ℝ≥0` be a non-negative real number.  `nnreal.normed r` or `r.normed` is the type of
finsupps `ℕ →₀ ℤ` with an extra parameter `r`.

The non-negative real number `r` is used in defining a norm on `r.normed`: given `F : ℕ →₀ ℤ`,
define `∥F∥₊ = ∑ x in F.support, ∥F x∥₊ * r⁻¹ ^ x`. -/
@[nolint unused_arguments, reducible, derive add_comm_group]
def nnreal.normed (r : ℝ≥0) := ℕ →₀ ℤ

namespace nnreal.normed
variable {r : ℝ≥0}

instance (r : ℝ≥0) : has_nnnorm r.normed :=
⟨λ F, ∑ x in F.support, ∥F x∥₊ * r⁻¹ ^ x⟩

@[simp]
lemma nnnorm_zero : ∥(0 : r.normed)∥₊ = 0 :=
by simp only [has_nnnorm.nnnorm, support_zero, sum_empty]

@[simp]
lemma nnnorm_neg (F : r.normed) :
  ∥-F∥₊ = ∥F∥₊ :=
by simp only [has_nnnorm.nnnorm, pi.neg_apply, coe_neg, support_neg, norm_neg]

lemma nnnorm_sub (F G : r.normed) :
  ∥F - G∥₊ = ∥G - F∥₊ :=
by rw [← nnnorm_neg (F - G), neg_sub]

lemma norm_dist (r : ℝ≥0) (j : ℕ) (x y : r.normed) : ∥x j - y j∥ = dist (x j) (y j) :=
by simp [has_norm.norm, has_dist.dist]

lemma nnnorm_add_le (F G : r.normed) :
  ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  unfold nnnorm,
  rw [sum_subset (subset_union_left _ _  : _ ⊆ F.support ∪ G.support),
      sum_subset (subset_union_right _ _ : _ ⊆ F.support ∪ G.support),
      sum_subset ((λ k hk, _) : _ ⊆ F.support ∪ G.support), ← finset.sum_add],
  { refine sum_le_sum (λ j hj, _),
    rw ← add_mul,
    refine mul_le_mul_of_nonneg_right _ (zero_le _),
    exact nnreal.coe_le_coe.mp (norm_add_le _ _) },
  repeat
  { intros k _ h, convert zero_mul _, simpa only [mem_support_iff, not_not, norm_eq_zero] using h },
  { simp only [mem_union, mem_support_iff, ne.def, finsupp.coe_add, pi.add_apply] at ⊢ hk,
    contrapose! hk,
    simp only [hk, add_zero] }
end

lemma nnnorm_triangle {r : ℝ≥0} (x y z : r.normed) : ∥x - z∥₊ ≤ ∥x - y∥₊ + ∥y - z∥₊ :=
by { convert nnnorm_add_le _ _, simp only [sub_add_sub_cancel] }

end nnreal.normed

/--  Let `r : ℝ≥0` be a non-negative real number and `S : Fintype` a finite type.
`invpoly r S` is the type of `S`-indexed terms of type `r.normed`, that is, finsupps
`ℕ →₀ ℤ` with norm defined using `r⁻¹`. -/
@[nolint unused_arguments, derive add_comm_group]
def invpoly (r : ℝ≥0) (S : Fintype) := S → r.normed

namespace invpoly
variables {r : ℝ≥0} {S : Fintype}

instance : inhabited (invpoly r S) := ⟨0⟩

instance : has_nnnorm (invpoly r S) :=
@sum_nnnorm S r.normed ⟨λ F, ∑ x in F.support, ∥F x∥₊ * r⁻¹ ^ x⟩

@[simp]
lemma nnnorm_zero : ∥(0 : invpoly r S)∥₊ = 0 :=
by simp only [sum_nnnorm_def, pi.zero_apply, sum_const_zero, nnreal.normed.nnnorm_zero]

@[simp]
lemma nnnorm_neg (F : invpoly r S) :
  ∥-F∥₊ = ∥F∥₊ :=
by simp only [sum_nnnorm_def, pi.neg_apply, nnreal.normed.nnnorm_neg]

lemma nnnorm_sub (F G : invpoly r S) :
  ∥F - G∥₊ = ∥G - F∥₊ :=
by rw [← nnnorm_neg (F - G), neg_sub]

lemma nnnorm_add_le (F G : invpoly r S) :
  ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  rw [sum_nnnorm_def, sum_nnnorm_def, sum_nnnorm_def, ← finset.sum_add],
  exact sum_le_sum (λ s hs, nnreal.normed.nnnorm_add_le _ _),
end

instance (S : Fintype) (r : ℝ≥0) : pseudo_normed_group (invpoly r S) :=
{ to_add_comm_group   := invpoly.add_comm_group r S,
  filtration          := λ c, {F : invpoly r S | ∥F∥₊ ≤ c},
  filtration_mono     := λ c d cd x (hx : ∥x∥₊ ≤ c), hx.trans cd,
  zero_mem_filtration := λ c, by simp only [set.mem_set_of_eq, nnnorm_zero, zero_le'],
  neg_mem_filtration  := λ c F hF, by simpa only [set.mem_set_of_eq, nnnorm_neg],
  add_mem_filtration  := λ c d F G hF hG, (nnnorm_add_le F G).trans (add_le_add hF hG) }

end invpoly
