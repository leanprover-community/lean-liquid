#exit
import for_mathlib.grading
import algebra.monoid_algebra

/-!

## Map to the monoid algebra

-/

namespace add_monoid_grading

open direct_sum

variables {A : Type*} [add_monoid A] [decidable_eq A] [decidable_eq A] {R : Type*} [ring R]
  (Mᵢ : A → add_submonoid R)
  [has_add_submonoid_decomposition Mᵢ] [add_submonoid.is_gmonoid Mᵢ]


noncomputable def to_monoid_algebra (Mᵢ : A → add_submonoid R)
  [has_add_submonoid_decomposition Mᵢ] [add_submonoid.is_gmonoid Mᵢ] :
  R →+* add_monoid_algebra R A :=
{ to_fun := λ r,
  { support := sorry,
    to_fun := λ m, add_submonoid_decomposition_ring_equiv Mᵢ r m,
    mem_support_to_fun := sorry },
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

end add_monoid_grading

section augmentation

namespace add_monoid_algebra

open direct_sum

variables {A : Type*} [add_monoid A] [decidable_eq A] {R : Type*} [ring R] (Mᵢ : A → add_submonoid R)
  [has_add_submonoid_decomposition Mᵢ] [add_submonoid.is_gmonoid Mᵢ]


def aug : add_monoid_algebra R A → R := λ f, finsupp.sum f (λ r m, m)

lemma aug_left_inverse (r : R) : aug (add_monoid_grading.to_monoid_algebra Mᵢ r) = r :=
begin
  sorry
end

end add_monoid_algebra

end augmentation
