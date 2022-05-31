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

lemma _root_.category_theory.is_zero_homology_iff_exact
  {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  is_zero (homology f g w) ↔ exact f g :=
begin
  rw preadditive.exact_iff_homology_zero,
  split,
  { intros h,
    use [w, h.iso_zero] },
  { rintros ⟨w,⟨h⟩⟩,
    apply is_zero.of_iso _ h,
    exact is_zero_zero _ }
end

lemma exact_of_is_zero_homology
  (h : ∀ i : ℤ, is_zero (C.homology i)) :
  ∀ i j k : ℤ, (complex_shape.down ℤ).rel i j → (complex_shape.down ℤ).rel j k →
  exact (C.d i j) (C.d j k) :=
begin
  rintros i j k ⟨rfl⟩ ⟨rfl⟩,
  dsimp,
  specialize h (k+1),
  erw _root_.category_theory.is_zero_homology_iff_exact at h,
  let e : C.X_prev (k+1) ≅ C.X (k+1+1) :=
    C.X_prev_iso rfl,
  let q : C.X_next (k+1) ≅ C.X k :=
    C.X_next_iso rfl,
  suffices : exact (e.hom ≫ C.d (k+1+1) (k+1)) (C.d (k+1) k ≫ q.inv),
  { simpa using this },
  dsimp [e,q], rwa [← C.d_to_eq, ← C.d_from_eq],
end

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

lemma homology_zero_iff_homology_zero :
  (∀ i : ℤ, is_zero (((homological_complex.embed $
    complex_shape.embedding.nat_down_int_down).obj D).homology i)) ↔
  (∀ i : ℕ, is_zero (D.homology i)) := sorry

universes v' u'

lemma homology_zero_iff_map_homology_zero
  {B : Type u'} [category.{v'} B] [abelian B] (E : A ≌ B)
  [E.functor.additive] :
  (∀ i : ℕ, is_zero (D.homology i)) ↔
  (∀ i : ℕ, is_zero (((E.functor.map_homological_complex _).obj D).homology i)) := sorry

end chain_complex
