import for_mathlib.grading
import algebra.monoid_algebra

/-!

## Map to the monoid algebra

-/

namespace monoid_grading

variables {M : Type*} [monoid M] [decidable_eq M] {R : Type*} [ring R]

noncomputable lemma foo (g : monoid_grading M R) : R →+* monoid_algebra R M :=
{ to_fun := λ r, { support := sorry,
  to_fun := λ m, g.decomposition r m,
  mem_support_to_fun := sorry },
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }


end monoid_grading
