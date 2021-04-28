import for_mathlib.grading
import algebra.monoid_algebra

/-!

## Map to the monoid algebra

-/

namespace monoid_grading

variables {M : Type*} [monoid M] [decidable_eq M] {R : Type*} [ring R]

noncomputable def to_monoid_algebra (g : monoid_grading M R) :
  R →+* monoid_algebra R M :=
{ to_fun := λ r,
  { support := sorry,
    to_fun := λ m, g.decomposition r m,
    mem_support_to_fun := sorry },
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

end monoid_grading

section augmentation

namespace monoid_algebra

variables {M : Type*} [monoid M] [decidable_eq M] {R : Type*} [ring R]

def aug : monoid_algebra R M → R := λ f, finsupp.sum f (λ r m, m)

lemma aug_left_inverse (g : monoid_grading M R) (r : R) : aug (g.to_monoid_algebra r) = r :=
begin
  sorry
end

end monoid_algebra

end augmentation
