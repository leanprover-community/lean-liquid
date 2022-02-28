import for_mathlib.Fintype
import pseudo_normed_group.basic
import Lbar.nnnorm_add_class

open finset finsupp
open_locale nnreal big_operators

noncomputable theory

section std_flt_lemmas
variables (α : Type*) [has_nnnorm α]

lemma std_flt_mono ⦃c d : ℝ≥0⦄ (cd : c ≤ d) :
  {z : α | ∥z∥₊ ≤ c} ⊆ {z : α | ∥z∥₊ ≤ d} :=
λ x (hx : ∥x∥₊ ≤ c), hx.trans cd

lemma std_flt_zero_mem [has_zero α] (n0 : ∥(0 : α)∥₊ = 0) (c : ℝ≥0) :
  (0 : α) ∈ {z : α | ∥z∥₊ ≤ c} :=
by simp only [n0, set.mem_set_of_eq, zero_le']

lemma std_flt_neg_mem [has_neg α] (nn : ∀ {x : α}, ∥- x∥₊ = ∥x∥₊) ⦃c : ℝ≥0⦄ ⦃x : α⦄
  (xc : x ∈ {z : α | ∥z∥₊ ≤ c}) :
  - x ∈ {z : α | ∥z∥₊ ≤ c} :=
by simpa only [nn, set.mem_set_of_eq] using xc

lemma std_flt_add_mem [has_add α] (n_le : ∀ {x y : α}, ∥x + y∥₊ ≤ ∥x∥₊ + ∥y∥₊) ⦃c d : ℝ≥0⦄ ⦃x y : α⦄
  (xc : x ∈ {z : α | ∥z∥₊ ≤ c}) (yd : y ∈ {z : α | ∥z∥₊ ≤ d}) :
  x + y ∈ {z : α | ∥z∥₊ ≤ c + d} :=
n_le.trans (add_le_add xc yd)

open nnnorm_add_class
variable {α}

/--  Given a type `α` with a `nnnorm_add_class` instance, `std_flt.to_pseudo_normed_group`
shows that the standard filtration `λ c, {z : α | ∥z∥₊ ≤ c}` endows `α` with a
`pseudo_normed_group` class. -/
def std_flt.to_pseudo_normed_group [add_comm_group α] [nnnorm_add_class α] :
  pseudo_normed_group α :=
{ filtration          := λ c, {z : α | ∥z∥₊ ≤ c},
  filtration_mono     := std_flt_mono α,
  zero_mem_filtration := std_flt_zero_mem α nnn_zero,
  neg_mem_filtration  := std_flt_neg_mem α nnn_neg,
  add_mem_filtration  := std_flt_add_mem α nnn_add_le }

end std_flt_lemmas


/--  Let `r : ℝ≥0` be a non-negative real number.  `nnreal.normed r` or `r.normed` is the type of
finsupps `ℕ →₀ ℤ` with an extra parameter `r`.

The non-negative real number `r` is used in defining a norm on `r.normed`: given `F : ℕ →₀ ℤ`,
define `∥F∥₊ = ∑ x in F.support, ∥F x∥₊ * r⁻¹ ^ x`. -/
@[nolint unused_arguments, reducible, derive add_comm_group]
def nnreal.normed (r : ℝ≥0) := ℕ →₀ ℤ

namespace nnreal.normed
variables {r : ℝ≥0} (F G H : r.normed)

instance (r : ℝ≥0) : has_nnnorm r.normed :=
⟨λ F, ∑ x in F.support, ∥F x∥₊ * r⁻¹ ^ x⟩

@[simp]
lemma nnnorm_zero : ∥(0 : r.normed)∥₊ = 0 :=
by simp only [has_nnnorm.nnnorm, support_zero, sum_empty]

@[simp]
lemma nnnorm_neg : ∥-F∥₊ = ∥F∥₊ :=
by simp only [has_nnnorm.nnnorm, pi.neg_apply, coe_neg, support_neg, norm_neg]

lemma nnnorm_add_le : ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
begin
  unfold nnnorm,
  rw [sum_subset (subset_union_left  F.support G.support),
      sum_subset (subset_union_right F.support G.support),
      sum_subset ((λ k, mem_union_support_of_mem_support_add F G) : _ ⊆ F.support ∪ G.support),
      ← finset.sum_add_distrib],
  { refine sum_le_sum (λ j hj, _),
    rw ← add_mul,
    exact mul_le_mul_of_nonneg_right (nnreal.coe_le_coe.mp (norm_add_le _ _)) (zero_le _) },
  repeat
  { simp only [mem_support_iff, not_not, norm_zero, mul_eq_zero, nonneg.mk_eq_zero,
      eq_self_iff_true, true_or, implies_true_iff] {contextual := true} }
end

instance : nnnorm_add_class r.normed :=
{ nnn_zero   := nnnorm_zero,
  nnn_neg    := nnnorm_neg,
  nnn_add_le := nnnorm_add_le,
  ..(infer_instance : add_comm_group _) }

instance : pseudo_normed_group r.normed :=
std_flt.to_pseudo_normed_group

end nnreal.normed

open nnnorm_add_class

variables {r : ℝ≥0} {α : Type*} [has_nnnorm α] {S : Fintype}

instance fintype.sum_nnnorm : has_nnnorm (S → α) :=
{ nnnorm := λ F, ∑ b, ∥F b∥₊ }

@[simp]
lemma fintype.sum_nnnorm_def (F : S → α) : ∥F∥₊ = ∑ b, ∥F b∥₊ := rfl

instance [add_group α] [nnnorm_add_class α] : nnnorm_add_class (S → α) :=
{ nnn_zero   := by simp,
  nnn_neg    := λ x, by simp [fintype.sum_nnnorm_def, pi.neg_apply, nnn_neg],
  nnn_add_le := λ F G, le_trans (sum_le_sum (λ j hj, nnnorm_add_le _ _)) sum_add_distrib.le,
  ..(infer_instance : add_comm_group _) }

/--  Let `r : ℝ≥0` be a non-negative real number and `S : Fintype` a finite type.
`invpoly r S` is the type of `S`-indexed terms of type `r.normed`, that is, finsupps
`ℕ →₀ ℤ` with norm defined using `r⁻¹`. -/
@[nolint unused_arguments, derive add_comm_group]
def invpoly (r : ℝ≥0) (S : Fintype) := S → r.normed

namespace invpoly

instance : inhabited (invpoly r S) := ⟨0⟩

instance : has_nnnorm (invpoly r S) :=
@fintype.sum_nnnorm r.normed ⟨nnnorm⟩ S

instance : nnnorm_add_class (invpoly r S) :=
pi.nnnorm_add_class

/-  The three lemmas
`variables (F G : invpoly r S)`
`@[simp] lemma nnnorm_zero : ∥(0 : invpoly r S)∥₊ = 0  := nnnorm_add_class.nnn_zero`
`@[simp] lemma nnnorm_neg  : ∥-F∥₊ = ∥F∥₊              := nnnorm_add_class.nnnorm_neg _`
`lemma nnnorm_add_le       : ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊    := nnnorm_add_class.nnnorm_add_le _ _`
follow from `nnnorm_add_class α`. -/

instance : pseudo_normed_group (invpoly r S) :=
std_flt.to_pseudo_normed_group

end invpoly
