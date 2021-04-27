/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import algebra.direct_sum
import group_theory.subgroup

/-!

# Grading of a ring by a monoid

A grading of a ring `R` by a monoid `M` is a decomposition R ≃ ⨁ Rₘ as an internal
direct sum of subgroups indexed by `m`, satisfying `1 ∈ R₀` and `RₘRₙ⊆R_{m+n}`

-/
-- MOVE
open_locale direct_sum

-- should be in algebra.direct_sum
lemma direct_sum.to_add_monoid_apply {ι : Type*} [decidable_eq ι]
  {β : ι → Type*} [Π (i : ι), add_comm_monoid (β i)]
  [ Π (i : ι) (x : β i), decidable (x ≠ 0)]
  {γ : Type*} [add_comm_monoid γ]
  (f : Π (i : ι), β i →+ γ) (b : ⨁ i, β i):
  direct_sum.to_add_monoid f b = dfinsupp.sum b (λ i, f i) :=
dfinsupp.sum_add_hom_apply _ _

-- should be in dfinsupp
namespace dfinsupp

variables (ι : Type*) (β : ι → Type*) [decidable_eq ι] [Π (j : ι), has_zero (β j)]
  (i : ι) (f : Π₀ i, β i)

lemma eq_single_iff : (∀ ⦃j : ι⦄, j ≠ i → f j = 0) ↔ dfinsupp.single i (f i) = f :=
⟨λ h, dfinsupp.ext $ λ j, begin
  by_cases hj : j = i,
  { subst hj,
    apply single_eq_same },
  { rw h hj,
    exact single_eq_of_ne (ne.symm hj) },
end,
begin
  rintro hf j h,
  rw ← hf,
  exact single_eq_of_ne h.symm,
end⟩

/-- A version of `dfinsupp.sum_single_index` which takes monoids homomorphisms. Useful for
  sometimes avoiding `@sum_single_index _ _ _ _ …`. -/
lemma add_monoid_hom_sum_single_index {ι : Type*} {β : ι → Type*} [decidable_eq ι]
  [_inst_1 : Π (i : ι), add_monoid (β i)]
  [_inst_2 : Π (i : ι) (x : β i), decidable (x ≠ 0)]
  {γ : Type*} [add_comm_monoid γ] {i : ι} {b : β i} {h : Π (i : ι), β i →+ γ} :
  (dfinsupp.single i b).sum (λ i, h i) = h i b :=
sum_single_index (h i).map_zero

end dfinsupp

/-

The below is in PR #7190 by Eric to algebra.direct_sum

-/

section Eric_PR

namespace direct_sum

variables {ι : Type*}

open_locale direct_sum

/-- The `direct_sum` formed by a collection of `add_submonoid`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →+ M` is bijective.
See `direct_sum.add_subgroup_is_internal` for the same statement about `add_subgroup`s. -/
def add_submonoid_is_internal {M : Type*} [decidable_eq ι] [add_comm_monoid M]
  (A : ι → add_submonoid M) : Prop :=
function.bijective (direct_sum.to_add_monoid (λ i, (A i).subtype) : (⨁ i, A i) →+ M)

/-- The `direct_sum` formed by a collection of `add_subgroup`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →+ M` is bijective.
See `direct_sum.submodule_is_internal` for the same statement about `submodules`s. -/
def add_subgroup_is_internal {M : Type*} [decidable_eq ι] [add_comm_group M]
  (A : ι → add_subgroup M) : Prop :=
function.bijective (direct_sum.to_add_monoid (λ i, (A i).subtype) : (⨁ i, A i) →+ M)

lemma add_subgroup_is_internal.to_add_submonoid
  {M : Type*} [decidable_eq ι] [add_comm_group M] (A : ι → add_subgroup M) :
  add_subgroup_is_internal A ↔
    add_submonoid_is_internal (λ i, (A i).to_add_submonoid) :=
iff.rfl

-- that's the end of Eric's PR but we seem to need more: we don't have the projections
-- as monoid homs

section unused_in_this_file

variables {M : Type*} [decidable_eq ι] [add_comm_monoid M] (A : ι → Type*)
  [∀ i, add_comm_monoid (A i)]

def projection (j : ι) : (⨁ i, A i) →+ A j :=
{ to_fun := λ f, f j,
  map_zero' := rfl,
  map_add' := λ x y, x.add_apply y j }

lemma projection_of_same (j : ι) (aj : A j) : projection A j (of (λ i, A i) j aj) = aj :=
@dfinsupp.single_eq_same _ _ _ _ j _

lemma projection_of_ne {i j : ι} (h : i ≠ j) (ai : A i) :
  projection A j (of (λ i, A i) i ai) = 0 :=
dfinsupp.single_eq_of_ne h

end unused_in_this_file

end direct_sum

end Eric_PR

/-- If `M` is an additive monoid, then an `M`-grading on a ring `R` is a decomposition of `R` as
    an internal direct sum `R = ⨁Rₘ` into submonoids indexed by `m : M`, where the decomposition
    respects `1` and `*`, in the sense that `1 ∈ R₀` and `Rₘ*Rₙ ⊆ R_{m+n}` -/
structure add_monoid_grading (M : Type*) [add_monoid M] [decidable_eq M] (R : Type*) [semiring R] :=
(pieces : M → add_submonoid R)
(direct_sum : direct_sum.add_submonoid_is_internal pieces)
(grading_one : (1 : R) ∈ pieces 0)
(grading_mul : ∀ (m n : M) (r s : R),
  r ∈ pieces m → s ∈ pieces n → r * s ∈ pieces (m + n))

/-- If `M` is a monoid, then an `M`-grading on a ring `R` is a decomposition of `R` as
    an internal direct sum `R = ⨁Rₘ` into submonoids indexed by `m : M`, where the decomposition
    respects `1` and `*`, in the sense that `1 ∈ R₁` and `Rₘ*Rₙ ⊆ R_{m*n}` -/
structure monoid_grading (M : Type*) [monoid M] [decidable_eq M] (R : Type*) [semiring R] :=
(pieces : M → add_submonoid R)
(is_direct_sum : direct_sum.add_submonoid_is_internal pieces)
(grading_one : (1 : R) ∈ pieces 1)
(grading_mul : ∀ (m n : M) (r s : R),
  r ∈ pieces m → s ∈ pieces n → r * s ∈ pieces (m * n))

attribute [to_additive] monoid_grading

namespace monoid_grading

/-! ## graded pieces -/

section graded_pieces

variables {M : Type*} [monoid M] [decidable_eq M] {R : Type*} [semiring R]

open_locale direct_sum

/-- The equivalence between R and ⨁ m, Rₘ if R is a graded (semi)ring. -/
@[to_additive "The equivalence between R and ⨁ m, Rₘ if R is a graded (semi)ring."]
noncomputable def decomposition (g : monoid_grading M R) :
  R ≃+ ⨁ m, g.pieces m :=
(add_equiv.of_bijective _ g.is_direct_sum).symm

/-- Decomposing `r` into `(rₘ)ₘ : ⨁ m, g.pieces m` and then adding the pieces gives `r` again. -/
lemma sum_decomposition (g : monoid_grading M R) (r : R) :
  (direct_sum.to_add_monoid (λ m, (g.pieces m).subtype) : (⨁ m, g.pieces m) →+ R)
    (g.decomposition r) = r :=
g.decomposition.symm_apply_apply r

/-- If `r ∈ Rₘ` then the element of `R` which is `r` at `m` and zero elsewhere, is `r`. -/
@[to_additive]
lemma eq_decomposition_of_mem_piece''' {g : monoid_grading M R} {r : R} {m : M}
  (hr : r ∈ g.pieces m) :
  (g.decomposition).symm (direct_sum.of (λ m, g.pieces m) m ⟨r, hr⟩) = r :=
begin
  change (direct_sum.to_add_monoid (λ m, (g.pieces m).subtype) : (⨁ m, (g.pieces m)) →+ R)
    (direct_sum.of (λ m, g.pieces m) m ⟨r, hr⟩) = r,
  rw direct_sum.to_add_monoid_of,
  refl,
end

/-- If `r ∈ Rₘ` then `r` is the element of `⨁Rₘ` which is `r` at `m` and `0` elsewhere. -/
@[to_additive]
lemma eq_decomposition_of_mem_piece'' {g : monoid_grading M R} {r : R} {m : M}
  (hr : r ∈ g.pieces m) :
  (g.decomposition) r = (direct_sum.of (λ m, g.pieces m) m ⟨r, hr⟩) :=
g.decomposition.eq_symm_apply.mp (eq_decomposition_of_mem_piece''' hr).symm

/-- If `r ∈ Rₘ` then `rₘ`, the `m`'th component of `r`, considered as an element of `Rₘ`, is `r`. -/
@[to_additive]
lemma eq_decomposition_of_mem_piece' {g : monoid_grading M R} {r : R} {m : M}
  (hr : r ∈ g.pieces m) :
  (g.decomposition) r m = ⟨r, hr⟩ :=
begin
  rw eq_decomposition_of_mem_piece'' hr,
  apply dfinsupp.single_eq_same,
end

/-- If `r ∈ Rₘ` then `rₘ`, the `m`'th component of `r`, considered as an element of `R`, is `r`. -/
@[to_additive]
lemma eq_decomposition_of_mem_piece {g : monoid_grading M R} {r : R} {m : M} (hr : r ∈ g.pieces m) :
  ((g.decomposition) r m : R) = r :=
begin
  rw eq_decomposition_of_mem_piece' hr,
  refl,
end

/-

## A note on decomposition

If `g : monoid_grading M R` and `r : R` then its `m`th component `rₘ` is `g.decomposition r m`

-/

-- let's test the API for grading
lemma mem_piece_iff_single_support {R : Type*} [semiring R] {M : Type*} [monoid M]
  [decidable_eq M] (g : monoid_grading M R) (r : R) (m : M) :
  r ∈ g.pieces m ↔ ∀ n, n ≠ m → g.decomposition r n = 0 :=
begin
  split,
  { intros hrm n hn,
    rw eq_decomposition_of_mem_piece'' hrm,
    exact direct_sum.projection_of_ne _ hn.symm _ },
  { intro h,
    rw dfinsupp.eq_single_iff at h,
    -- can't use `classical` because `decidable_eq M` gets lost
    letI : ∀ n, decidable_eq (g.pieces n) := λ _, classical.dec_eq _,
    rw [← g.sum_decomposition r, direct_sum.to_add_monoid_apply, ← h,
        dfinsupp.add_monoid_hom_sum_single_index],
    exact (g.decomposition r m).2 }
end

end graded_pieces

/-!

## rings are graded by subgroups

If a ring (or even an add_comm_group) is an internal direct sum of add_submonoids
then they're all add_subgroups.

-/

variables {M : Type*} [monoid M] [decidable_eq M] {R : Type*} [ring R]

-- to_additive can't handle this for some reason so I need to prove it twice
/-- A monoid_grading on a ring be add_submonoids is in fact by add_subgroups -/
def add_subgroup_pieces (g : monoid_grading M R) (m : M) : add_subgroup R :=
{ neg_mem' := λ x hx, begin
    change -x ∈ g.pieces m,
    convert (g.decomposition (-x) m).2,
    apply neg_eq_of_add_eq_zero,
    --  x ∈ Rₘ so (g.decomposition x).to_finsupp m = x.
    nth_rewrite 0 ← eq_decomposition_of_mem_piece hx,
    rw subtype.val_eq_coe,
    norm_cast,
    suffices : (g.decomposition x + g.decomposition (-x)) m  = 0,
      simp only [*, add_submonoid.coe_zero, direct_sum.add_apply] at *,
    simp [← (g.decomposition).map_add],
  end,
  ..g.pieces m}

end monoid_grading

namespace add_monoid_grading

def add_subgroup_pieces {M : Type*} [add_monoid M] [decidable_eq M]
  {R : Type*} [ring R]  (g : add_monoid_grading M R) (m : M) : add_subgroup R :=
{ neg_mem' := λ x hx, begin
-- same proof as above :-(
    change -x ∈ g.pieces m,
    convert (g.decomposition (-x) m).2,
    apply neg_eq_of_add_eq_zero,
    --  x ∈ Rₘ so (g.decomposition x).to_finsupp m = x.
    nth_rewrite 0 ← eq_decomposition_of_mem_piece hx,
    rw subtype.val_eq_coe,
    norm_cast,
    suffices : (g.decomposition x + g.decomposition (-x)) m  = 0,
      simp only [*, add_submonoid.coe_zero, direct_sum.add_apply] at *,
    simp [← (g.decomposition).map_add],
  end,
  ..g.pieces m}

attribute [to_additive monoid_grading.add_subgroup_pieces] add_subgroup_pieces

end add_monoid_grading
