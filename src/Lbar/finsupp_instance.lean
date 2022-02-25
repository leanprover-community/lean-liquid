import pseudo_normed_group.basic
import category_theory.Fintype
import analysis.normed_space.basic

open finset finsupp
open_locale nnreal big_operators

noncomputable theory

universes u v

section families_of_add_comm_groups

-- `apply_instance` works.  Having this instance explicitly, allows `finsupp_add_group` to work.
instance add_comm_group_finsupp {α β γ : Type*} [add_comm_group γ] : add_comm_group (α → β →₀ γ) :=
pi.add_comm_group

--  Without the explicit instance `add_comm_group_finsupp`, this does not work
instance finsupp_add_group (S : Type*) : add_comm_group (S → ℤ →₀ ℝ) := by apply_instance

/--  A function from a `Fintype` is automatically a `finsupp`, when the target has a zero. -/
def finsupp_of_fintype_domain {α : Type*} [has_zero α] {S : Fintype} (F : S → α) : S →₀ α :=
{ support            := (set.finite.of_fintype {s | F s ≠ 0}).to_finset,
  to_fun             := F,
  mem_support_to_fun := by simp }

lemma finset.sum_add {α β : Type*} [add_comm_monoid β] {F G : α → β} (s : finset α) :
  ∑ x in s, (F x + G x) = ∑ x in s, F x + ∑ x in s, G x :=
begin
  classical,
  refine finset.induction_on s (by simp) (λ a s as h, _),
  rw [sum_insert as, sum_insert as, sum_insert as, h],
  abel,
end

instance fintype.sum_nnnorm {S : Fintype} {α : Type*} [has_nnnorm α] : has_nnnorm (S → α) :=
{ nnnorm := λ F, ∑ s, ∥F s∥₊ }

instance sum_nnnorm (S : Fintype) (α : Type*) [has_nnnorm α] :
  has_nnnorm (S → α) :=
{ nnnorm := λ F, ∑ b, ∥F b∥₊ }

@[simp]
lemma sum_nnnorm_def {S : Fintype} {α : Type*} [has_nnnorm α] (F : S → α) :
  ∥F∥₊ = ∑ b, ∥F b∥₊ := rfl

lemma sum_nnnorm_add_le {S : Fintype} {β : Type*} [semi_normed_group β]
  (F G : S → β) :
  ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  simp only [sum_nnnorm_def, pi.add_apply],
  exact le_trans (sum_le_sum (λ i hi, nnnorm_add_le _ _)) (finset.sum_add _).le,
end

end families_of_add_comm_groups

lemma add_zero_dists {α β : Type*} [decidable_eq α] [add_zero_class β] {l : α} {x y z : α →₀ β}
  (h : x l + y l + z l = 0) (hl : l ∈ x.support) :
  l ∈ y.support ∪ z.support :=
begin
  contrapose hl,
  simp only [mem_support_iff, coe_sub, pi.sub_apply, ne.def, not_not, mem_union] at hl ⊢,
  push_neg at hl,
  cases hl with h1 h2,
  rwa [h1, h2, add_zero, add_zero] at h,
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

/-  This instance, in particular, provides a `pseudo_metric_space` instance to `r.normed`. -/
instance (r : ℝ≥0) : semi_normed_group r.normed :=
{ norm          := coe ∘ has_nnnorm.nnnorm,
  dist          := λ F G, ∥F - G∥₊,
  dist_self     := λ F, by simp only [sub_self, nnnorm_zero, nonneg.coe_zero],
  dist_comm     := λ F G, by simp only [dist, nnnorm_sub],
  dist_triangle := λ x y z, begin
    unfold dist has_nnnorm.nnnorm,
    norm_cast,
    rw [sum_subset (subset_union_left _ _ : _ ⊆ (x - y).support ∪ (y - z).support),
      sum_subset (subset_union_right _ _ : _ ⊆ (x - y).support ∪ (y - z).support),
      sum_subset (λ l hl, dists hl : _ ⊆ (_ - y).support ∪ _), ← finset.sum_add],
    { refine sum_le_sum (λ j hj, _),
      rw ← add_mul,
      refine mul_le_mul_of_nonneg_right _ (zero_le _),
      apply nnreal.coe_le_coe.mp,
      simpa only [coe_sub, pi.sub_apply, subtype.coe_mk, norm_dist] using dist_triangle _ _ _ },
    repeat { intros k hk hh,
      convert zero_mul _,
      simpa only [mem_support_iff, not_not, norm_eq_zero] using hh }
  end,
  edist_dist := λ x y, by simp only [subtype.coe_eta, ennreal.of_real_coe_nnreal],
  dist_eq := λ x y, by simp only,
  ..(infer_instance : add_comm_group _) }

end nnreal.normed

/--  Let `r : ℝ≥0` be a non-negative real number and `S : Fintype` a finite type.
`invpoly r S` is the type of `S`-indexed terms of type `r.normed`, that is, finsupps
`ℕ →₀ ℤ` with norm defined using `r⁻¹`. -/
@[nolint unused_arguments, derive add_comm_group]
def invpoly (r : ℝ≥0) (S : Fintype) := S → r.normed

namespace invpoly
variables {r : ℝ≥0} {S : Fintype}

instance : inhabited (invpoly r S) := ⟨0⟩

instance (r : ℝ≥0) (S : Fintype) : has_nnnorm (invpoly r S) :=
@sum_nnnorm S r.normed ⟨λ F, ∑ x in F.support, ∥F x∥₊ * r⁻¹ ^ x⟩

@[simp]
lemma nnnorm_zero {r : ℝ≥0} {S : Fintype} : ∥(0 : invpoly r S)∥₊ = 0 :=
by simp only [sum_nnnorm_def, pi.zero_apply, sum_const_zero, nnreal.normed.nnnorm_zero]

@[simp]
lemma nnnorm_neg {r : ℝ≥0} {S : Fintype} (F : invpoly r S) :
  ∥-F∥₊ = ∥F∥₊ :=
by simp only [sum_nnnorm_def, pi.neg_apply, nnreal.normed.nnnorm_neg]

lemma nnnorm_sub {r : ℝ≥0} {S : Fintype} (F G : invpoly r S) :
  ∥F - G∥₊ = ∥G - F∥₊ :=
by rw [← nnnorm_neg (F - G), neg_sub]

instance {r : ℝ≥0} {S : Fintype} : topological_space (invpoly r S) :=
by simpa only [invpoly] using preorder.topology _

instance {r : ℝ≥0} {S : Fintype} : semi_normed_group (invpoly r S) :=
{ norm          := coe ∘ has_nnnorm.nnnorm,
  dist          := λ F G, ∥F - G∥₊,
  dist_self     := λ F, by simp only [sub_self, nnnorm_zero, nonneg.coe_zero],
  dist_comm     := λ F G, by simp only [dist, nnnorm_sub],
  dist_triangle := λ x y z, show ∑ s, ∥x s - z s∥₊ ≤ ∑ s, ∥x s - y s∥₊ + ∑ (x : ↥S), ∥y x - z x∥₊, by
  { refine (sum_le_sum (λ s hs, _)).trans (finset.sum_add _).le,
    exact dist_triangle (x s) (y s) (z s) },
  edist_dist    := λ x y, by simp only [subtype.coe_eta, ennreal.of_real_coe_nnreal],
  dist_eq       := λ x y, by simp only,
  ..(infer_instance : add_comm_group _) }

--  There is some awkwardness in getting the fact that the `nnnorm` instances coincide.
--  you can see this in the `convert sum_nnnorm_add_le F G` step.
instance (S : Fintype) (r : ℝ≥0) : pseudo_normed_group (invpoly r S) :=
{ to_add_comm_group   := by refine invpoly.add_comm_group r S,
  filtration          := λ c, {F : invpoly r S | ∥F∥₊ ≤ c},
  filtration_mono     := λ c d cd x hx, by { rw set.mem_set_of_eq at hx ⊢, exact hx.trans cd },
  zero_mem_filtration := λ c,
    by { simp only [set.mem_set_of_eq, nnnorm_zero, zero_le'] },
  neg_mem_filtration  := λ c F hF, by simpa only [set.mem_set_of_eq, nnnorm_neg],
  add_mem_filtration  := λ c d F G hF hG, begin
      simp only [sum_nnnorm_def, set.mem_set_of_eq, pi.add_apply, finsupp.coe_add],
      refine le_trans _ (add_le_add hF hG),
      convert sum_nnnorm_add_le F G,
      { ext s, simp only [pi.add_apply, _root_.coe_nnnorm], refl },
      repeat { unfold invpoly.has_nnnorm, congr, ext, refl },
    end }

end invpoly
