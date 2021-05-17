/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Eric Wieser
-/
import algebra.direct_sum
import group_theory.subgroup
import algebra.direct_sum_graded
import group_theory.submonoid.operations

/-!

# Gradings

Internal gradings of add_comm_monoids, add_comm_groups, semirings and rings.

The simplest example of the set-up: we have an `add_comm_monoid R` and an indexed family
`Mᵢ : ι → add_submonoid R`. The function `Mᵢ` is a *grading* of `R`
if the induced map `⨁ Mᵢ i →+ R` is an isomorphism.

Variants:

* `R` is an `add_comm_group` and `Gᵢ : ι → add_subgroup R`
* `R` is a `semiring` and `Mᵢ : ι → add_submonoid R` and `ι` is itself an add_monoid,
  such that `1 ∈ Mᵢ 0` and `Mᵢ i * Mᵢ j ⊆ Mᵢ (i + j)`
* `R` is a `ring` and `Gᵢ : ι → add_subgroup R` and `ι` is an add_monoid
  such that `1 ∈ Gᵢ 0` and `Gᵢ i * Gᵢ j ⊆ Gᵢ (i + j)`.

## TODO

list main definitions etc

-/

-- MOVE -- not sure I use it
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

/-- A version of `dfinsupp.sum_single_index` which takes monoid homomorphisms. Useful for
  sometimes avoiding `@sum_single_index _ _ _ _ …`. -/
lemma add_monoid_hom_sum_single_index {ι : Type*} {β : ι → Type*} [decidable_eq ι]
  [_inst_1 : Π (i : ι), add_monoid (β i)]
  [_inst_2 : Π (i : ι) (x : β i), decidable (x ≠ 0)]
  {γ : Type*} [add_comm_monoid γ] {i : ι} {b : β i} {h : Π (i : ι), β i →+ γ} :
  (dfinsupp.single i b).sum (λ i, h i) = h i b :=
sum_single_index (h i).map_zero

lemma sum_eq_zero {ι : Type*} {M : ι → Type*} {N : Type*}
  [decidable_eq ι] [has_add ι] [Π (i : ι), add_comm_monoid (M i)] [add_comm_monoid N]
  [Π (i : ι) (x : M i), decidable (x ≠ 0)]
  (x : Π₀ i, M i)
  (f : Π (i : ι), M i → N) (h : ∀ i, x i ≠ 0 → f i (x i) = 0) :
  x.sum f = 0 :=
finset.sum_eq_zero $ λ i hi, h _ $ (x.mem_support_iff i).1 hi

end dfinsupp

-- If we add this lemma, we should add it for all subobjects
lemma add_submonoid.not_mem_or_of_add_not_mem
  {M : Type*} [add_monoid M] (S : add_submonoid M) {x y : M} :
  x + y ∉ S → x ∉ S ∨ y ∉ S :=
begin
  rw ←not_and_distrib,
  exact mt (λ h, S.add_mem h.1 h.2),
end

namespace direct_sum

variables {ι : Type*}

open_locale direct_sum

variables {M : Type*} [decidable_eq ι] [add_comm_monoid M] (A : ι → Type*)
  [∀ i, add_comm_monoid (A i)]

/-- Add_monoid_hom version of the projection from a direct sum to a factor. -/
def proj (j : ι) : (⨁ i, A i) →+ A j :=
{ to_fun := λ f, f j,
  map_zero' := rfl,
  map_add' := λ x y, x.add_apply y j }

lemma proj_of_same (j : ι) (aj : A j) : proj A j (of (λ i, A i) j aj) = aj :=
@dfinsupp.single_eq_same _ _ _ _ j _

lemma proj_of_same' (j k : ι) (h : j = k) (aj : A j) :
  proj A k (of (λ i, A i) j aj) = cast (show A j = A k, by rw h) aj :=
begin
  subst h,
  convert proj_of_same A j _,
end

lemma eval_of_same (j : ι) (aj : A j) : (of (λ i, A i) j aj) j = aj :=
@dfinsupp.single_eq_same _ _ _ _ j _

lemma eval_of_same' (j k : ι) (h : j = k) (aj : A j) :
  (of (λ i, A i) j aj) k = cast (show A j = A k, by rw h) aj :=
begin
  subst h,
  convert eval_of_same A j _,
end

lemma proj_of_ne {i j : ι} (h : i ≠ j) (ai : A i) :
  proj A j (of (λ i, A i) i ai) = 0 :=
dfinsupp.single_eq_of_ne h

lemma eval_of_ne {i j : ι} (h : i ≠ j) (ai : A i) : (of (λ i, A i) i ai) j = 0 :=
proj_of_ne _ h ai

open_locale direct_sum big_operators

-- TODO: does this unfold too far or not enough?
lemma mul_apply {ι : Type*} {A : ι → Type*}
  [decidable_eq ι] [has_add ι] [Π (i : ι), add_comm_monoid (A i)] [direct_sum.ghas_mul A]
  [Π (i : ι) (x : A i), decidable (x ≠ 0)]
  (x y : ⨁ i, A i) (i : ι) :
    (x * y) i = x.sum (λ xi xv, y.sum (λ yi yv,
      if h : xi + yi = i then cast (congr_arg _ h) (ghas_mul.mul xv yv) else 0 )) :=
begin
  dsimp[(*), direct_sum.mul_hom, to_add_monoid_apply],
  simp only [add_monoid_hom.dfinsupp_sum_apply, to_add_monoid_apply, dfinsupp.sum_apply,
    add_monoid_hom.flip_apply, add_monoid_hom.comp_apply, add_monoid_hom.comp_hom_apply_apply],
  congr' with xi xv,
  congr' with yi yv,
  dsimp [direct_sum.of],
  rw dfinsupp.single_apply,
  congr' with h,
  cases h,
  refl,
end

end direct_sum

open_locale direct_sum

open function

namespace direct_sum

/-!
### Gradings by `add_submonoid`s
-/
section add_submonoid

/-!
#### `add_submonoid`s of an `add_comm_monoid` indexed by a type
-/
section add_comm_monoid

variables {ι : Type*} [decidable_eq ι] {M : Type*} [add_comm_monoid M] (Mᵢ : ι → add_submonoid M)

-- TODO : I want to call this proj.
/-- The canonical map from a direct sum of `add_submonoid`s to their carrier type-/
abbreviation to_add_monoid_carrier : (⨁ i, Mᵢ i) →+ M :=
(to_add_monoid $ λ i, (Mᵢ i).subtype)

/-- A class to indicate that the collection of submonoids `Mᵢ` make up an internal direct
sum. -/
class has_add_submonoid_decomposition :=
(components : M → ⨁ i, Mᵢ i)
(left_inv : left_inverse (to_add_monoid_carrier Mᵢ) components)
(right_inv : right_inverse (to_add_monoid_carrier Mᵢ) components)

/- The decomposition provided by a `has_add_submonoid_decomposition` as an `add_equiv`. -/
def add_submonoid_decomposition [has_add_submonoid_decomposition Mᵢ] : M ≃+ ⨁ i, Mᵢ i :=
add_equiv.symm {
  inv_fun := (direct_sum.has_add_submonoid_decomposition.components : M → ⨁ i, Mᵢ i),
  left_inv := has_add_submonoid_decomposition.right_inv,
  right_inv := has_add_submonoid_decomposition.left_inv,
  ..(to_add_monoid_carrier Mᵢ) }

/-- By definition a `add_submonoid_decomposition` makes up an internal direct sum. -/
lemma add_submonoid_decomposition.is_internal [has_add_submonoid_decomposition Mᵢ] :
  add_submonoid_is_internal Mᵢ :=
(add_submonoid_decomposition Mᵢ).symm.bijective

/-- Noncomputably construct a decomposition from a proof the direct sum is an internal direct
sum. -/
noncomputable def add_submonoid_is_internal.has_decomposition (h : add_submonoid_is_internal Mᵢ) :
  has_add_submonoid_decomposition Mᵢ :=
{ components := (equiv.of_bijective _ h).symm,
  ..(equiv.of_bijective _ h).symm}

end add_comm_monoid

/-!
#### `add_submonoid`s of a `semiring` indexed by an `add_monoid`

Remark: should probably also index them by `monoid`s
-/
section semiring

variables {A R : Type*} [decidable_eq A] [add_monoid A] [semiring R] (Mᵢ : A → add_submonoid R)

/-- A class to indicate that a collection of `add_submonoid`s meet the requirements of
`direct_sum.gmonoid`. -/
class add_submonoid.is_gmonoid : Prop :=
(grading_one : (1 : R) ∈ Mᵢ 0)
(grading_mul : ∀ {m n : A} {r s : R}, r ∈ Mᵢ m → s ∈ Mᵢ n → r * s ∈ Mᵢ (m + n))

/-- TODO: perhaps `gmonoid.of_add_submonoids` should be merged with this. -/
instance add_submonoid.is_gmonoid.gmonoid [add_submonoid.is_gmonoid Mᵢ] : gmonoid (λ i, Mᵢ i) :=
gmonoid.of_add_submonoids _ add_submonoid.is_gmonoid.grading_one $
  λ i j ⟨a, ha⟩ ⟨b, hb⟩, add_submonoid.is_gmonoid.grading_mul ha hb

/-- A decomposition of submonoids of a ring preserves multiplication. -/
lemma to_add_monoid_carrier_mul [has_add_submonoid_decomposition Mᵢ] [add_submonoid.is_gmonoid Mᵢ]
  (x y : ⨁ i, Mᵢ i) :
  to_add_monoid_carrier Mᵢ (x * y) =
    to_add_monoid_carrier Mᵢ x * to_add_monoid_carrier Mᵢ y :=
begin
    -- nasty `change` tricks to get things to a point where we can use `ext`. `induction` on `f`
  -- and `g` may be easier.
  change (to_add_monoid_carrier Mᵢ).comp (add_monoid_hom.mul_left x) y =
    (add_monoid_hom.mul_left $
      (to_add_monoid_carrier Mᵢ) x).comp (to_add_monoid_carrier Mᵢ) y,
  apply add_monoid_hom.congr_fun,
  ext yi yv : 2,
  let y' := direct_sum.of _ yi yv,
  change (to_add_monoid_carrier Mᵢ).comp (add_monoid_hom.mul_right y') x =
    (add_monoid_hom.mul_right $
      (to_add_monoid_carrier Mᵢ) y').comp (to_add_monoid_carrier Mᵢ) x,
  apply add_monoid_hom.congr_fun,
  ext xi xv : 2,
  let x' := direct_sum.of _ xi xv,
  change to_add_monoid_carrier Mᵢ (x' * y') =
    to_add_monoid_carrier Mᵢ x' * to_add_monoid_carrier Mᵢ y',
  dsimp only [x', y'],
  dunfold to_add_monoid_carrier,
  rw of_mul_of,
  simp only [to_add_monoid_of],
  refl,
end

-- TODO Even better -- this is an R₀-algebra hom
/-- `direct_sum.add_submonoid_decomposition` as a `ring_equiv`. -/
def add_submonoid_decomposition_ring_equiv
  [has_add_submonoid_decomposition Mᵢ] [add_submonoid.is_gmonoid Mᵢ] :
  R ≃+* ⨁ i, Mᵢ i :=
ring_equiv.symm
{ map_mul' := to_add_monoid_carrier_mul Mᵢ,
  ..(add_submonoid_decomposition Mᵢ).symm}

end semiring

section comm_semiring

variables {A : Type*} [decidable_eq A] [add_comm_monoid A]
  {R : Type*} [comm_semiring R] (Mᵢ : A → add_submonoid R)

/-- TODO: perhaps `gcomm_monoid.of_add_submonoids` should be merged with this. -/
instance add_submonoid.is_gmonoid.gcomm_monoid [add_submonoid.is_gmonoid Mᵢ] :
  gcomm_monoid (λ i, Mᵢ i) :=
gcomm_monoid.of_add_submonoids _ add_submonoid.is_gmonoid.grading_one $
  λ i j ⟨a, ha⟩ ⟨b, hb⟩, add_submonoid.is_gmonoid.grading_mul ha hb
end comm_semiring

end add_submonoid

/-!
### Gradings by `add_subgroup`s
-/
section add_subgroup

/-!
#### `add_subgroups`s of an `add_comm_group` indexed by a type
-/
section add_comm_group

variables {ι : Type*} [decidable_eq ι] {G : Type*} [add_comm_group G] (Gᵢ : ι → add_subgroup G)

/-- The canonical map from a direct sum of `add_submonoid`s to their carrier type-/
abbreviation to_add_group_carrier : (⨁ i, Gᵢ i) →+ G :=
(to_add_monoid $ λ i, (Gᵢ i).subtype)

/-- A class to indicate that the collection of subgroups `Gᵢ` make up an internal direct
sum. -/
class has_add_subgroup_decomposition :=
(components : G → ⨁ i, Gᵢ i)
(left_inv : left_inverse (to_add_group_carrier Gᵢ) components)
(right_inv : right_inverse (to_add_group_carrier Gᵢ) components)

instance add_subgroup.has_add_subgroup_decomposition_to_has_add_submonoid_decomposition
  [i : has_add_subgroup_decomposition Gᵢ] :
  has_add_submonoid_decomposition (λ (a : ι), (Gᵢ a).to_add_submonoid) :=
{ components := i.components,
  left_inv := by convert i.left_inv,
  right_inv := by convert i.right_inv }

/- The decomposition provided by a `has_add_subgroup_decomposition` as an `add_equiv`. -/
def add_subgroup_decomposition [has_add_subgroup_decomposition Gᵢ] : G ≃+ ⨁ i, Gᵢ i :=
add_equiv.symm {
  inv_fun := (direct_sum.has_add_subgroup_decomposition.components : G → ⨁ i, Gᵢ i),
  left_inv := has_add_subgroup_decomposition.right_inv,
  right_inv := has_add_subgroup_decomposition.left_inv,
  ..(to_add_group_carrier Gᵢ) }

/-- By definition a `add_subgroup_decomposition` makes up an internal direct sum. -/
lemma add_subgroup_decomposition.is_internal [has_add_subgroup_decomposition Gᵢ] :
  add_subgroup_is_internal Gᵢ :=
(add_subgroup_decomposition Gᵢ).symm.bijective

/-- Noncomputably construct a decomposition from a proof the direct sum is an internal direct
sum. -/
noncomputable def add_subgroup_is_internal.has_decomposition (h : add_subgroup_is_internal Gᵢ) :
  has_add_subgroup_decomposition Gᵢ :=
{ components := (equiv.of_bijective _ h).symm,
  ..(equiv.of_bijective _ h).symm}

end add_comm_group

/-!
#### `add_subgroups`s of a `ring` indexed by an add_monoid

Remark: should probably also index them by `monoid`s
-/
section ring

variables {A : Type*} [decidable_eq A] [add_monoid A]
  {R : Type*} [ring R] (Gᵢ : A → add_subgroup R)

/-- A class to indicate that a collection of `add_subgroup`s meet the requirements of
`direct_sum.gmonoid`. -/
class add_subgroup.is_gmonoid : Prop :=
(grading_one : (1 : R) ∈ Gᵢ 0)
(grading_mul : ∀ {m n : A} {r s : R},
  r ∈ Gᵢ m → s ∈ Gᵢ n → r * s ∈ Gᵢ (m + n))

instance add_subgroup.is_gmonoid.gmonoid [add_subgroup.is_gmonoid Gᵢ] : gmonoid (λ i, Gᵢ i) :=
gmonoid.of_add_subgroups _ add_subgroup.is_gmonoid.grading_one $
  λ i j ⟨a, ha⟩ ⟨b, hb⟩, add_subgroup.is_gmonoid.grading_mul ha hb

instance add_subgroup.is_gmonoid_to_add_submonoid.is_gmonoid [add_subgroup.is_gmonoid Gᵢ] :
  add_submonoid.is_gmonoid (λ (a : A), (Gᵢ a).to_add_submonoid) :=
{ grading_one := add_subgroup.is_gmonoid.grading_one ,
  grading_mul := λ _ _ _ _, add_subgroup.is_gmonoid.grading_mul }

/-- A decomposition of submonoids of a ring preserves multiplication. -/
lemma to_add_group_carrier_mul [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ]
  (x y : ⨁ i, Gᵢ i) :
  to_add_group_carrier Gᵢ (x * y) =
    to_add_group_carrier Gᵢ x * to_add_group_carrier Gᵢ y :=
by convert to_add_monoid_carrier_mul (λ (a : A), (Gᵢ a).to_add_submonoid) x y

/-- `direct_sum.add_subgroup_decomposition` as a `ring_equiv`. -/
def add_subgroup_decomposition_ring_equiv
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] :
  R ≃+* ⨁ i, Gᵢ i :=
ring_equiv.symm
{ map_mul' := to_add_group_carrier_mul Gᵢ,
  ..(add_subgroup_decomposition Gᵢ).symm}

end ring

section comm_ring

variables {A : Type*} [decidable_eq A] [add_comm_monoid A]
  {R : Type*} [comm_ring R] (Gᵢ : A → add_subgroup R)

instance add_subgroup.is_gmonoid.gcomm_monoid [add_subgroup.is_gmonoid Gᵢ] :
  gcomm_monoid (λ i, Gᵢ i) :=
gcomm_monoid.of_add_subgroups _ add_subgroup.is_gmonoid.grading_one $
  λ i j ⟨a, ha⟩ ⟨b, hb⟩, add_subgroup.is_gmonoid.grading_mul ha hb

end comm_ring

end add_subgroup

/-! ## graded pieces for a grading by `add_submonoid`s -/

namespace has_add_submonoid_decomposition

open_locale direct_sum

open direct_sum

variables {A : Type*} [decidable_eq A] {R : Type*} [add_comm_monoid R]
  (Mᵢ : A → add_submonoid R) [has_add_submonoid_decomposition Mᵢ]

/-- Decomposing `r` into `(rᵢ)ᵢ : ⨁ i, Mᵢ i` and then adding the pieces gives `r` again. -/
lemma sum_decomposition (r : R) :
  (direct_sum.to_add_monoid (λ i, (Mᵢ i).subtype) : (⨁ i, Mᵢ i) →+ R)
    (add_submonoid_decomposition Mᵢ r) = r :=
(add_submonoid_decomposition Mᵢ).symm_apply_apply r

variable {Mᵢ}

/-- If `r ∈ Rₘ` then the element of `R` which is `r` at `m` and zero elsewhere, is `r`. -/
lemma eq_decomposition_of_mem_piece''' {r : R} {i : A}
  (hr : r ∈ Mᵢ i) :
  (add_submonoid_decomposition Mᵢ).symm (direct_sum.of (λ i, Mᵢ i) i ⟨r, hr⟩) = r :=
begin
  change (direct_sum.to_add_monoid (λ i, (Mᵢ i).subtype) : (⨁ i, (Mᵢ i)) →+ R)
    (direct_sum.of (λ i, Mᵢ i) i ⟨r, hr⟩) = r,
  rw direct_sum.to_add_monoid_of,
  refl,
end

/-- If `r ∈ Rₘ` then `r` is the element of `⨁Rₘ` which is `r` at `m` and `0` elsewhere. -/
lemma eq_decomposition_of_mem_piece'' {r : R} {i : A}
  (hr : r ∈ Mᵢ i) :
  add_submonoid_decomposition Mᵢ r = (direct_sum.of (λ i, Mᵢ i) i ⟨r, hr⟩) :=
(add_submonoid_decomposition Mᵢ).to_equiv.eq_symm_apply.mp
  (eq_decomposition_of_mem_piece''' hr).symm

/-- If `r ∈ Rₘ` then `rₘ`, the `m`'th component of `r`, considered as an element of `Rₘ`, is `r`. -/
lemma eq_decomposition_of_mem_piece' {r : R} {i : A} (hr : r ∈ Mᵢ i) :
  add_submonoid_decomposition Mᵢ r i = ⟨r, hr⟩ :=
begin
  rw eq_decomposition_of_mem_piece'' hr,
  apply dfinsupp.single_eq_same,
end

/-- If `r ∈ Rₘ` then `rₘ`, the `m`'th component of `r`, considered as an element of `R`, is `r`. -/
lemma eq_decomposition_of_mem_piece {r : R} {i : A} (hr : r ∈ Mᵢ i) :
  (add_submonoid_decomposition Mᵢ r i : R) = r :=
begin
  rw eq_decomposition_of_mem_piece' hr,
  refl,
end

lemma mem_piece_iff_single_support (r : R) (i : A) :
  r ∈ Mᵢ i ↔ ∀ ⦃j⦄, j ≠ i → add_submonoid_decomposition Mᵢ r j = 0 :=
begin
  split,
  { intros hrm n hn,
    rw eq_decomposition_of_mem_piece'' hrm,
    exact direct_sum.proj_of_ne _ hn.symm _ },
  { intro h,
    rw dfinsupp.eq_single_iff at h,
    -- can't use `classical` because `decidable_eq M` gets lost
    letI : ∀ n, decidable_eq (Mᵢ n) := λ _, classical.dec_eq _,
    rw [← sum_decomposition Mᵢ r, direct_sum.to_add_monoid_apply, ← h,
        dfinsupp.add_monoid_hom_sum_single_index],
    exact (add_submonoid_decomposition Mᵢ r i).2 }
end

lemma mem_piece_iff_proj_eq (r : R) (i : A) :
  r ∈ Mᵢ i ↔ (add_submonoid_decomposition Mᵢ r i : R) = r :=
⟨eq_decomposition_of_mem_piece, begin
  intro h,
  rw ←h,
  exact (((add_submonoid_decomposition Mᵢ) r) i).2,
end⟩

variable (Mᵢ)

def internal_proj (i : A) : R →+ R :=
{ to_fun := λ r, add_submonoid_decomposition Mᵢ r i,
  map_zero' := by simp,
  map_add' := by simp
}

variable {Mᵢ}

lemma internal_proj_apply (i : A) (r : R) :
  internal_proj Mᵢ i r = add_submonoid_decomposition Mᵢ r i := rfl

-- WTF type class inference??

-- lemma sum_internal_proj [Π i (x : (λ (i : A), ↥(Mᵢ i)) i), decidable (x ≠ 0)] (r : R) (i : A) :
--   finset.sum (add_submonoid_decomposition Mᵢ r).support (λ i, internal_proj Mᵢ i r) = 0 := sorry

section classical
-- break yury's rule of thimb
open_locale classical

/-- Decomposing `r` into `(rᵢ)ᵢ : ⨁ i, Mᵢ i` and then adding the pieces gives `r` again. -/
lemma sum_internal_proj [Π i (x : (λ (i : A), ↥(Mᵢ i)) i), decidable (x ≠ 0)] (r : R) (i : A) :
   finset.sum (add_submonoid_decomposition Mᵢ r).support (λ i, internal_proj Mᵢ i r) = r :=
begin
  conv_rhs {rw ← sum_decomposition Mᵢ r},
  simp_rw internal_proj_apply,
  generalize : (add_submonoid_decomposition Mᵢ) r = s,
  apply direct_sum.induction_on s; clear i s,
  { refl },
  { intros,
    simp only [add_submonoid.coe_subtype, to_add_monoid_of],
    by_cases hx : x = 0, { subst hx, simp },
    unfold of,
    unfold dfinsupp.single_add_hom,
    dsimp,
    change x ≠ 0 at hx,
--    rw dfinsupp.support_single_ne_zero hx, doesn't work??
    rw dfinsupp.support_single_ne_zero, swap, assumption,
    simp },
  { intros x y hx hy,
    simp only [←hx, ←hy, add_monoid_hom.map_add, add_apply, add_submonoid.coe_add],
    -- bleurgh should be in API
    suffices : dfinsupp.sum (x + y) (λ i, (Mᵢ i).subtype) =
      dfinsupp.sum x (λ i, (Mᵢ i).subtype) + dfinsupp.sum y (λ i, (Mᵢ i).subtype),
    { convert this, simp },
    rw dfinsupp.sum_add_index,
    { intros, refl },
    { intros, refl } }
end

end classical

end has_add_submonoid_decomposition

/-! ## graded pieces for a grading by `add_group`s -/

namespace has_add_subgroup_decomposition

open_locale direct_sum

open direct_sum

variables {A : Type*} [decidable_eq A] {R : Type*} [add_comm_group R]
  (Gᵢ : A → add_subgroup R) [has_add_subgroup_decomposition Gᵢ]

/-- Decomposing `r` into `(rᵢ)ᵢ : ⨁ i, Mᵢ i` and then adding the pieces gives `r` again. -/
lemma sum_decomposition  (r : R) :
  (direct_sum.to_add_monoid (λ i, (Gᵢ i).subtype) : (⨁ i, Gᵢ i) →+ R)
    (add_subgroup_decomposition Gᵢ r) = r :=
(add_subgroup_decomposition Gᵢ).symm_apply_apply r

variable {Gᵢ}

/-- If `r ∈ Rₘ` then the element of `R` which is `r` at `m` and zero elsewhere, is `r`. -/
lemma eq_decomposition_of_mem_piece''' {r : R} {i : A}
  (hr : r ∈ Gᵢ i) :
  (add_subgroup_decomposition Gᵢ).symm (direct_sum.of (λ i, Gᵢ i) i ⟨r, hr⟩) = r :=
begin
  change (direct_sum.to_add_monoid (λ i, (Gᵢ i).subtype) : (⨁ i, (Gᵢ i)) →+ R)
    (direct_sum.of (λ i, Gᵢ i) i ⟨r, hr⟩) = r,
  rw direct_sum.to_add_monoid_of,
  refl,
end

/-- If `r ∈ Rₘ` then `r` is the element of `⨁Rₘ` which is `r` at `m` and `0` elsewhere. -/
lemma eq_decomposition_of_mem_piece'' {r : R} {i : A}
  (hr : r ∈ Gᵢ i) :
  add_subgroup_decomposition Gᵢ r = (direct_sum.of (λ i, Gᵢ i) i ⟨r, hr⟩) :=
(add_subgroup_decomposition Gᵢ).to_equiv.eq_symm_apply.mp
  (eq_decomposition_of_mem_piece''' hr).symm

/-- If `r ∈ Rₘ` then `rₘ`, the `m`'th component of `r`, considered as an element of `Rₘ`, is `r`. -/
lemma eq_decomposition_of_mem_piece' {r : R} {i : A} (hr : r ∈ Gᵢ i) :
  add_subgroup_decomposition Gᵢ r i = ⟨r, hr⟩ :=
begin
  rw eq_decomposition_of_mem_piece'' hr,
  apply dfinsupp.single_eq_same,
end

/-- If `r ∈ Rₘ` then `rₘ`, the `m`'th component of `r`, considered as an element of `R`, is `r`. -/
lemma eq_decomposition_of_mem_piece {r : R} {i : A} (hr : r ∈ Gᵢ i) :
  (add_subgroup_decomposition Gᵢ r i : R) = r :=
begin
  rw eq_decomposition_of_mem_piece' hr,
  refl,
end

lemma mem_piece_iff_single_support (r : R) (i : A) :
  r ∈ Gᵢ i ↔ ∀ ⦃j⦄, j ≠ i → add_subgroup_decomposition Gᵢ r j = 0 :=
show r ∈ (Gᵢ i).to_add_submonoid ↔ ∀ ⦃j⦄, j ≠ i → add_submonoid_decomposition (λ i, (Gᵢ i).to_add_submonoid) r j = 0,
by convert has_add_submonoid_decomposition.mem_piece_iff_single_support r i

lemma mem_piece_iff_proj_eq (r : R) (i : A) :
  r ∈ Gᵢ i ↔ (add_subgroup_decomposition Gᵢ r i : R) = r :=
⟨eq_decomposition_of_mem_piece, begin
  intro h,
  rw ←h,
  exact (((add_subgroup_decomposition Gᵢ) r) i).2,
end⟩

-- ring_equiv version
lemma mem_piece_iff_proj_eq'
  {A : Type u_1} [decidable_eq A] [add_monoid A]
  {R : Type u_2} [ring R]
  {Gᵢ : A → add_subgroup R} [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ]
(r : R) (i : A) :
  r ∈ Gᵢ i ↔ (add_subgroup_decomposition_ring_equiv Gᵢ r i : R) = r :=
mem_piece_iff_proj_eq r i

end has_add_subgroup_decomposition

section external_stuff

open_locale direct_sum

variables {ι : Type*} [decidable_eq ι]
  {M : Type*} [add_comm_monoid M]
  (A : ι → Type*) [Π (i : ι), add_comm_monoid (A i)]


@[simps apply]
def apply_add_monoid_hom (i) : (⨁ i, A i) →+ A i :=
{ to_fun := λ f, f i,
  map_add' := λ f g, begin rw dfinsupp.coe_add, refl, end,
  map_zero' := rfl}

lemma of_mul_apply [add_left_cancel_monoid ι] [gmonoid A] (b : ⨁ i, A i) (i j : ι) (m : A i) :
  (mul_hom A (of A i m) b) (i + j) = ghas_mul.mul m (b j) :=
begin
  -- direct_sum has no good induction tactics, so the game is to rearrange to a point that `ext` can apply
  change direct_sum.apply_add_monoid_hom A (i + j) (mul_hom A (of A i m) b) =
    ghas_mul.mul m (direct_sum.apply_add_monoid_hom A j b),
  repeat { rw ←add_monoid_hom.comp_apply},
  refine add_monoid_hom.congr_fun _ b,
  ext bi bx,
  let b := direct_sum.of A bi bx,
  change (mul_hom A (of A i m) b) (i + j) = ghas_mul.mul m (b j),
  dsimp only [b],

  -- ok, now we just have to clean up
  rw mul_hom_of_of,
  simp only [direct_sum.of, dfinsupp.single_add_hom_apply] at ⊢ b,
  by_cases h : bi = j,
  { subst h,
    rw [dfinsupp.single_eq_same, dfinsupp.single_eq_same] },
  rw dfinsupp.single_eq_of_ne h,
  rw dfinsupp.single_eq_of_ne (λ h', h $ add_left_cancel h'),
  rw add_monoid_hom.map_zero,
end

theorem mul_single_component [add_left_cancel_monoid ι] [gmonoid A]
  (b : ⨁ i, A i) (i j : ι) (m : A i) :
  of A (i + j) (((of A i m) * b) (i + j)) = of A i m * of A j (b j) :=
begin
  rw of_mul_of,
  dsimp only,
  congr,
  exact of_mul_apply A b i j m,
end

-- let's try this one with induction
theorem mul_single_component' [add_right_cancel_monoid ι] [gmonoid A]
  (b : ⨁ i, A i) (i j : ι) (m : A j) :
  of A (i + j) ((b * (of A j m)) (i + j)) = of A i (b i) * of A j m :=
begin
  apply direct_sum.induction_on b,
  { simp },
  { intros k ak,
    rw of_mul_of,
    by_cases h : i = k,
    { subst h,
      rw eval_of_same,
      rw of_mul_of,
      rw eval_of_same },
    { have h2 : i + j ≠ k + j,
        intro h3, apply h, apply add_right_cancel h3,
      rw eval_of_ne A h2.symm,
      rw eval_of_ne A (ne.symm h),
      simp } },
  { intros x y hx hy,
    rw add_mul,
    change (of A (i + j)) (apply_add_monoid_hom A (i + j) (x * (of A j) m + y * (of A j) m)) = _,
    rw add_monoid_hom.map_add,
    rw add_monoid_hom.map_add,
    change (of A (i + j)) ((x * (of A j) m) (i + j)) +
  (of A (i + j)) ((y * (of A j) m) (i + j)) = _,
    rw [hx, hy],
    simp [add_mul] }
end

end external_stuff

/-!

## A grading of an `add_comm_group` by `add_submonoid`s is in fact a grading by `add_subgroup`s.

If an `add_comm_group` is an internal direct sum of `add_submonoid`s
then they're all `add_subgroup`s. Possibly useful for filling in the `neg_mem` field
when grading an `add_comm_group` by `add_subgroup`s?

-/

namespace has_add_submonoid_decomposition

open direct_sum

-- M is an add_comm_group now, not an add_comm_monoid

variables {ι : Type*} [decidable_eq ι] {M : Type*} [add_comm_group M]
  (Mᵢ : ι → add_submonoid M) [has_add_submonoid_decomposition Mᵢ]

/-- If an `add_comm_group` is graded by `add_submonoid`s, they're all closed
  under negation. -/
theorem neg_mem {i : ι} {x : M}
  (hx : x ∈ Mᵢ i) : -x ∈ Mᵢ i :=
begin
    convert (add_submonoid_decomposition Mᵢ (-x) i).2,
    apply neg_eq_of_add_eq_zero,
    --  x ∈ Rₘ so (add_submonoid_decomposition Mᵢ).to_finsupp m = x.
    nth_rewrite 0 ← eq_decomposition_of_mem_piece hx,
    rw subtype.val_eq_coe,
    norm_cast,
    suffices : (add_submonoid_decomposition Mᵢ x +
      add_submonoid_decomposition Mᵢ (-x)) i  = 0,
      simp only [*, add_submonoid.coe_zero, direct_sum.add_apply] at *,
    simp [← (add_submonoid_decomposition Mᵢ).map_add],
end


end has_add_submonoid_decomposition

end direct_sum
