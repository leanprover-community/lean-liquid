import pseudo_normed_group.basic
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

open_locale nnreal

lemma mem_union_support_of_mem_support_add {α β : Type*} [add_zero_class β] [decidable_eq α] {k : α}
  (F G : α →₀ β) (hk : k ∈ (F + G).support) :
  k ∈ F.support ∪ G.support :=
begin
  simp only [finset.mem_union, finsupp.mem_support_iff, finsupp.coe_add, pi.add_apply] at ⊢ hk,
  contrapose! hk,
  simp only [hk, add_zero],
end

variables (α : Type*) [has_nnnorm α]

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

namespace nnnorm_add_class
variables {α}

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
