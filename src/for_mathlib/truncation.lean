import for_mathlib.imker

noncomputable theory

open category_theory category_theory.limits

namespace cochain_complex

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables (C : cochain_complex 𝓐 ℤ)

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

lemma ι_iso (i : ℤ) (hC : ((homotopy_category.quotient _ _).obj C).bounded_by (i+1)) :
  is_iso (truncation.ι C i) :=
sorry

-- feel free to skip this, and directly provide a defn for `ι_succ` below
def map_of_le (i j : ℤ) (h : i ≤ j) : C.truncation i ⟶ C.truncation j :=
sorry

def ι_succ (i : ℤ) : C.truncation i ⟶ C.truncation (i+1) :=
truncation.map_of_le _ _ _ $ by simp only [le_add_iff_nonneg_right, zero_le_one]

def to_imker (i : ℤ) : C.truncation i ⟶ imker C i :=
sorry

lemma short_exact_ι_succ_to_imker (i : ℤ) :
  ∀ n, short_exact ((ι_succ C i).f n) ((to_imker C (i+1)).f n) :=
sorry

end truncation

end cochain_complex
