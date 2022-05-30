import algebra.homology.homology
import category_theory.abelian.exact
import category_theory.limits.shapes.zero_objects
import for_mathlib.complex_extend

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

namespace chain_complex

variables (C : chain_complex A ℤ)

/- This whole file is SELFCONTAINED -/

lemma exact_of_is_zero_homology
  (h : ∀ i : ℤ, is_zero (C.homology i)) :
  ∀ i j k : ℤ, (complex_shape.down ℤ).rel i j → (complex_shape.down ℤ).rel j k →
  exact (C.d i j) (C.d j k) := sorry

lemma is_zero_homology_of_exact
  (h : ∀ i j k : ℤ, (complex_shape.down ℤ).rel i j → (complex_shape.down ℤ).rel j k →
  exact (C.d i j) (C.d j k)) :
  ∀ i : ℤ, is_zero (C.homology i) := sorry

lemma exact_iff_is_zero_homology :
  (∀ i : ℤ, is_zero (C.homology i)) ↔
  (∀ i j k : ℤ, (complex_shape.down ℤ).rel i j → (complex_shape.down ℤ).rel j k →
  exact (C.d i j) (C.d j k)) :=
⟨exact_of_is_zero_homology _, is_zero_homology_of_exact _⟩

variable (D : chain_complex A ℕ)

lemma epi_and_exact_of_is_zero_homology
  (h : ∀ i : ℤ,
    is_zero (((homological_complex.embed $
    complex_shape.embedding.nat_down_int_down).obj D).homology i)) :
  epi (D.d 1 0) ∧ ∀ i : ℕ, exact (D.d (i+2) (i+1)) (D.d (i+1) (i)) := sorry

lemma is_zero_homology_of_epi_and_exact
  (h1 : epi (D.d 1 0))
  (h2 : ∀ i : ℕ, exact (D.d (i+2) (i+1)) (D.d (i+1) (i))) :
  ∀ i : ℤ, is_zero (((homological_complex.embed $
    complex_shape.embedding.nat_down_int_down).obj D).homology i) := sorry

lemma epi_and_exact_iff_is_zero_homology :
  (epi (D.d 1 0) ∧ ∀ i : ℕ, exact (D.d (i+2) (i+1)) (D.d (i+1) (i))) ↔
  (∀ i : ℤ, is_zero (((homological_complex.embed $
    complex_shape.embedding.nat_down_int_down).obj D).homology i)) :=
⟨λ h, is_zero_homology_of_epi_and_exact D h.1 h.2,
  epi_and_exact_of_is_zero_homology _⟩

end chain_complex
