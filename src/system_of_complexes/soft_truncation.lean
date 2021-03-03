import system_of_complexes.basic
import for_mathlib.normed_group_quotient

/-!
# Soft truncation

In this file we define soft truncation functors
for (systems of) complexes of normed groups.

We call these `soft_truncation'` to distinguish them from the usual soft truncation functors.
The difference is solely in the definition of the object in degree `0`.
Usually this object is defined as `C 0` modulo the kernel of `d : C 0 ⟶ C 1`.
Instead, we define it as `C 0` modulo the image of `d : C (-1) ⟶ C 0`.
Hence the two definitions agree iff `C` is exact in degree `0`.

-/

noncomputable theory
open_locale nnreal

open category_theory category_theory.limits

namespace NormedGroup
open quotient_add_group

namespace soft_truncation'

-- Note: the next sorry needs a `NormedGroup`, so we need to bundle.
def X (C : cochain_complex NormedGroup) : ℤ → NormedGroup
| -[1+n]  := 0
| 0       := NormedGroup.of $ quotient (C.d (-1)).range.topological_closure
| (n+1:ℕ) := C.X (n+1)

def d (C : cochain_complex NormedGroup) :
  Π i:ℤ, X C i ⟶ X C (i+1)
| -[1+n]  := 0
| 0       := sorry -- some quotient.lift
| (n+1:ℕ) := C.d (n+1)

lemma d_squared' (C : cochain_complex NormedGroup) :
  Π i:ℤ, d C i ≫ d C (i+1) = 0
| -[1+n]  := show 0 ≫ _ = 0, by rw zero_comp
| 0       := sorry
| (n+1:ℕ) := C.d_squared (n+1)

@[simps]
def obj (C : cochain_complex NormedGroup) :
  cochain_complex NormedGroup :=
{ X := X C,
  d := d C,
  d_squared' := funext $ d_squared' C }

def map_f {C₁ C₂ : cochain_complex NormedGroup} (f : C₁ ⟶ C₂) :
  Π i:ℤ, X C₁ i ⟶ X C₂ i
| -[1+n]  := 0
| 0       := sorry -- some quotient.lift or quotient.map ??
| (n+1:ℕ) := f.f (n+1)

lemma map_comm {C₁ C₂ : cochain_complex NormedGroup} (f : C₁ ⟶ C₂) :
  Π i:ℤ, d C₁ i ≫ map_f f (i+1) = map_f f i ≫ d C₂ i
| -[1+n]  := show 0 ≫ _ = _ ≫ 0, by rw [zero_comp, comp_zero]
| 0       := sorry -- some quotient.lift or quotient.map ??
| (n+1:ℕ) := homological_complex.comm_at f (n+1)

def map {C₁ C₂ : cochain_complex NormedGroup} (f : C₁ ⟶ C₂) :
  obj C₁ ⟶ obj C₂ :=
{ f := map_f f,
  comm' := funext $ map_comm f }

end soft_truncation'

@[simps]
def soft_truncation' : cochain_complex NormedGroup ⥤ cochain_complex NormedGroup :=
{ obj := λ C, soft_truncation'.obj C,
  map := λ C₁ C₂ f, soft_truncation'.map f,
  map_id' := sorry,
  map_comp' := sorry }

end NormedGroup

namespace system_of_complexes

variables (C : system_of_complexes)

@[simps]
def soft_truncation' : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ NormedGroup.soft_truncation'

lemma soft_truncation'_d_neg (c : ℝ≥0) (i : ℤ) (hi : i < 0) :
  (d : (soft_truncation'.obj C) c i ⟶ _) = 0 := sorry

variables (k K : ℝ≥0) (m : ℤ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0)
include hk

lemma soft_truncation'_is_bounded_exact_iff
  (hC : ∀ c, (d : (soft_truncation'.obj C) c (-2) ⟶ _) = 0) :
  (soft_truncation'.obj C).is_bounded_exact k K m c₀ ↔ C.is_bounded_exact k K m c₀ :=
sorry

lemma soft_truncation'_is_weak_bounded_exact_iff
  (hC : ∀ c, (d : (soft_truncation'.obj C) c (-2) ⟶ _) = 0) :
  (soft_truncation'.obj C).is_weak_bounded_exact k K m c₀ ↔ C.is_weak_bounded_exact k K m c₀ :=
sorry


/-
TODO

* lemmas for how `has_shift` interacts with bounded exactness
-/

end system_of_complexes
