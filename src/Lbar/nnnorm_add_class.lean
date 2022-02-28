import pseudo_normed_group.basic
import category_theory.Fintype
import analysis.normed_space.basic

/-!
Let `α` be a type with the structure of an additive commutative group and
a non-negative norm `∥_∥₊`.

In this file, we introduce
* the typeclass `nnnorm_add_class α`,
* a construction of `pseudo_normed_group` using the "standard filtration" `λ c, {z : α | ∥z∥₊ ≤ c}`.

##  The typeclass `nnnorm_add_class α`
Given an additive commutative group `α` with a `nnnorm`, the typeclass `nnnorm_add_class α`
requires to prove the identities:
* the nnnorm of `0` is `0` : `∥0∥₊ = 0`;
* the nnnorm of `-x` is equal to the nnnorm of `x`: `∥- x∥₊ = ∥x∥₊`;
* the nnnorm of a sum is at most the sum of the nnnorms: `∥x + y∥₊ ≤ ∥x∥₊ + ∥y∥₊`.

##  The standard filtration `c : ℝ≥0 ↦ {z : α | ∥z∥₊ ≤ c}`
Let `α` be a nnnormed type.  We use the naming convention `std_flt` for the function `ℝ≥0 → set α`
taking a non-negative real number `c` to the subset of all the terms of `α` of nnnorm at most `c`:
```
ℝ≥0 → set α
  c ↦ {z : α | ∥z∥₊ ≤ c}.
```

The main construction is `std_flt.to_pseudo_normed_group` asserting that the typeclass
`nnnorm_add_class α` (i.e. `α` is an additive commutative group with a compatible `∥_∥₊`),
gives rise to a `pseudo_normed_group α` under the standard filtration.
-/

open finset finsupp
open_locale nnreal big_operators

lemma mem_union_support_of_mem_support_add {α β : Type*} [add_zero_class β] [decidable_eq α] {k : α}
  (F G : α →₀ β) (hk : k ∈ (F + G).support) :
  k ∈ F.support ∪ G.support :=
begin
  simp only [mem_union, mem_support_iff, ne.def, finsupp.coe_add, pi.add_apply] at ⊢ hk,
  contrapose! hk,
  simp only [hk, add_zero],
end

variables (α : Type*) [has_nnnorm α]
section std_flt_lemmas

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

end std_flt_lemmas

/--  A typeclass for an additive commutative group with a nnnorm.  Its fields assert that
* the nnnorm of `0` is `0`;
* the nnnorm of `-x` is equal to the nnnorm of `x`;
* the nnnorm of a sum is at most the sum of the nnnorms.
The class assumes `add_comm_group`, since this is what is required for `pseudo_normed_group`.
-/
@[ancestor add_comm_group has_nnnorm]
class nnnorm_add_class [has_zero α] [has_add α] [has_neg α] : Prop :=
(nnn_zero   : ∥(0 : α)∥₊ = 0)
(nnn_neg    : ∀ ⦃x : α⦄, ∥- x∥₊ = ∥x∥₊)
(nnn_add_le : ∀ ⦃x y : α⦄, ∥x + y∥₊ ≤ ∥x∥₊ + ∥y∥₊)

variables {α}
namespace nnnorm_add_class

section def_lemmas
variables [has_zero α] [has_add α] [has_neg α] [nnnorm_add_class α]

@[simp] lemma nnnorm_zero : ∥(0 : α)∥₊ = 0 := nnn_zero

@[simp] lemma nnnorm_neg (x : α) : ∥- x∥₊ = ∥x∥₊ :=
by apply nnn_neg

lemma nnnorm_add_le (x y : α) : ∥x + y∥₊ ≤ ∥x∥₊ + ∥y∥₊ :=
by apply nnn_add_le

end def_lemmas

variables [add_group α] [nnnorm_add_class α]
lemma nnnorm_sub (x y : α) : ∥x - y∥₊ = ∥y - x∥₊ :=
by rw [← nnnorm_neg, neg_sub]

lemma nnnorm_triangle (x y z : α) : ∥x - z∥₊ ≤ ∥x - y∥₊ + ∥y - z∥₊ :=
(le_of_eq (by simp only [sub_add_sub_cancel])).trans (nnnorm_add_le _ _)

end nnnorm_add_class

open nnnorm_add_class

section std_flt_instances
variables {S : Fintype}

instance fintype.sum_nnnorm : has_nnnorm (S → α) :=
{ nnnorm := λ F, ∑ b, ∥F b∥₊ }

@[simp]
lemma fintype.sum_nnnorm_def (F : S → α) : ∥F∥₊ = ∑ b, ∥F b∥₊ := rfl

variables {β : Type*} [add_group β] [has_nnnorm β] [nnnorm_add_class β]

instance : nnnorm_add_class (S → β) :=
{ nnn_zero   := by simp,
  nnn_neg    := λ x, by simp [fintype.sum_nnnorm_def, pi.neg_apply, nnn_neg],
  nnn_add_le := λ F G, le_trans (sum_le_sum (λ j hj, nnnorm_add_le _ _)) sum_add_distrib.le,
  ..(infer_instance : add_comm_group _) }

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

end std_flt_instances
