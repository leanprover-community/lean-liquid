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

-- change of variables ideas
lemma is_zero_homology_of_exact
  (h : ∀ i j k : ℤ, (complex_shape.down ℤ).rel i j → (complex_shape.down ℤ).rel j k →
  exact (C.d i j) (C.d j k)) :
  ∀ i : ℤ, is_zero (C.homology i) :=
begin
  intro i,
  specialize h (i+1) i (i-1) rfl (sub_add_cancel i 1),
  rw _root_.category_theory.is_zero_homology_iff_exact,
  rw ← homological_complex.X_prev_iso_comp_d_to at h, swap, simp,
  rw ← homological_complex.d_from_comp_X_next_iso at h, swap, simp,
  simpa only [exact_comp_iso, exact_iso_comp] using h,
end

/-

kmb experiments  -- happy to delete

-- change of variables ideas
lemma is_zero_homology_of_exact
  (h : ∀ i j k : ℤ, (complex_shape.down ℤ).rel i j → (complex_shape.down ℤ).rel j k →
  exact (C.d i j) (C.d j k)) :
  ∀ i : ℤ, is_zero (C.homology i) :=
begin
  -- For stupid defeq reasons coming up later on we want to change
  -- variables

  -- this has a name (it's `f 1` for some `f`) but I can't find it.
  let eij : ℤ ≃ ℤ := ⟨λ i, i - 1, λ j, j + 1,
  λ i, sub_add_cancel i 1, λ j, add_tsub_cancel_right _ _⟩,
  -- Make the abstract change of variables claim
  suffices : ∀ (j : ℤ), is_zero (homological_complex.homology C (eij.symm j)),
  --
  { intro i,
    -- use the equiv the other way
    specialize this (eij i),
    -- the simplifier can take it from here (avoiding motive not type correct errors)
    simpa, },
  -- now unravel the equiv
  dsimp [eij],
  -- and forget it
  clear eij,
  /-
  alternative approach involves changing goal to ∀ i, P((i - 1) + 1)
  and then generalizing (i - 1) to j, but then you're rewriting under binders,
  TODO: try other way
  -/
  /-
  Third approach (working code below) : instead of defining eij just do the
  rewrite more brutally. I didn't like how you couldn't get rid of i afterwards
  until you introduced j.

  -- convenient to have i of the form k+1 for stupid
  -- definitional reasons so let's start by changing variables.
  have k := i - 1,
  have hk : k = i - 1 := by refl,
  have hi : i = k + 1 := by {rw hk, ring },
  -- That's our bijections between the `i` and `k` world.
  rw hi, -- change all the i's to k's
  -- Define a new variable j to be "k, but forget about whole "defined
  -- in terms of i" part".
  generalize : k = j,
  -- We'll do the entire rest of the problem with the abstract
  -- variable j. We tidy up, for no particular reason.
  clear hi hk k i,
  -/
  intro k,
  rw _root_.category_theory.is_zero_homology_iff_exact,
  specialize h (k+1+1) (k+1) k rfl rfl,
  /-
  h: exact (C.d (i + 1) i) (C.d i (i - 1))
  ⊢ exact (homological_complex.d_to C i) (homological_complex.d_from C i)
  -/
  convert h,
  -- gives me `heq`s
  repeat {sorry },
end

-/

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
  epi (D.d 1 0) ∧ ∀ i : ℕ, exact (D.d (i+2) (i+1)) (D.d (i+1) (i)) :=
begin
  split,
  { specialize h 0,
  rw [category_theory.is_zero_homology_iff_exact,
    homological_complex.d_from_eq _ (show (complex_shape.down ℤ).rel 0 (-1), by simp),
    exact_comp_iso, homological_complex.d_to_eq _ (show (complex_shape.down ℤ).rel 1 0, by simp),
    exact_iso_comp] at h,
    rw is_zero.eq_zero_of_tgt (is_zero_zero _)
      (((homological_complex.embed complex_shape.embedding.nat_down_int_down).obj D).d 0 (-1)) at h,
    rw epi_iff_exact_zero_right,
    exact h, -- defeq abuse probably
  },
  { intro i,
    specialize h (i + 1 : ℕ),
    rw [category_theory.is_zero_homology_iff_exact,
      homological_complex.d_from_eq _ (show (complex_shape.down ℤ).rel (i + 1 : ℕ) (i : ℕ), by simp),
      exact_comp_iso, homological_complex.d_to_eq _ (show (complex_shape.down ℤ).rel (i + 2 : ℕ) (i + 1 : ℕ), by simp),
      exact_iso_comp] at h,
    exact h, }, -- more defeq abuse
end


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
