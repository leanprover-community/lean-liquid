import algebra.homology.homological_complex
import algebra.homology.single
import category_theory.abelian.basic
import for_mathlib.split_exact
import for_mathlib.derived.defs

noncomputable theory

open category_theory category_theory.limits

namespace cochain_complex

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables (C : cochain_complex 𝓐 ℤ)

/--
Given a cochain complex
```
C^{n-2} → C^{n-1} → C^n → C^{n+1}
```
`imker C n` should be the cochain complex
```
   0  → Im(d^n) → Ker(d^n) → 0
```
As a result, `H_i(imker C n) = 0` for all `i≠n` and `= H_i(C)` for `i=n`.
-/
def imker (C : cochain_complex 𝓐 ℤ) (n : ℤ) : cochain_complex 𝓐 ℤ :=
sorry

namespace imker

open homological_complex (single)

/-- The natural map from `H_n(C)[n]` to `imker C n`. -/
def from_single (n : ℤ) : (single _ _ n).obj (C.homology n) ⟶ C.imker n :=
sorry

instance from_single_quasi_iso (n : ℤ) :
  homotopy_category.is_quasi_iso $ (homotopy_category.quotient _ _).map (from_single C n) :=
sorry

end imker

/--
This should be the canonical truncation functor `τ_{≤n}` for cochain complexes.
It is the functor (3) in the second set of truncation functors on this page:
https://stacks.math.columbia.edu/tag/0118
-/
def truncation (C : cochain_complex 𝓐 ℤ) (i : ℤ) : cochain_complex 𝓐 ℤ :=
sorry

namespace truncation

lemma bounded_by (i : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.truncation i)).bounded_by (i+1) :=
sorry

instance is_bounded_above (i : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.truncation i)).is_bounded_above :=
⟨⟨i+1, bounded_by C i⟩⟩

def ι (i : ℤ) : C.truncation i ⟶ C :=
sorry

-- feel free to skip this, and directly provide a defn for `succ_ι` below
def map_of_le (i j : ℤ) (h : i ≤ j) : C.truncation i ⟶ C.truncation j :=
sorry

def succ_ι (i : ℤ) : C.truncation i ⟶ C.truncation (i+1) :=
truncation.map_of_le _ _ _ $ by simp only [le_add_iff_nonneg_right, zero_le_one]

def to_imker (i : ℤ) : C.truncation i ⟶ imker C i :=
sorry

lemma short_exact_succ_ι_to_imker (i : ℤ) :
  ∀ n, short_exact ((succ_ι C i).f n) ((to_imker C (i+1)).f n) :=
sorry

end truncation

end cochain_complex
