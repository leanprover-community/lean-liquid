import for_mathlib.derived.defs
import for_mathlib.homological_complex_op

noncomputable theory

open category_theory
open homotopy_category

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {ι : Type*} {c : complex_shape ι}

-- SELFCONTAINED
lemma is_quasi_iso_of_op {X Y : (homological_complex 𝓐 c)ᵒᵖ} (f : X ⟶ Y)
  (h : is_quasi_iso ((homotopy_category.quotient _ _).map
    (homological_complex.op_functor.map f))) :
  is_quasi_iso ((homotopy_category.quotient _ _).map f.unop) :=
begin
  sorry
end
