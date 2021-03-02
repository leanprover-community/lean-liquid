import system_of_complexes.basic
import for_mathlib.extend_from_nat

noncomputable theory
open_locale nnreal

namespace system_of_complexes

variables (C : system_of_complexes)

def shift_obj_fun (c : ℝ≥0) : ℕ → NormedGroup
| 0     := sorry -- cokernel of `d : C c 0 ⟶ C c 1`
| (n+1) := C c (n+2)

/-
TODO
* turn this into a system_of_complexes
* ?? turn it into a functor?
* show that if `d : C c (-1) ⟶ C c 0` is `0`, then
  `shift C` is bounded exact `≤ m - 1` if and only if C is so `≤ m`.
-/

end system_of_complexes
