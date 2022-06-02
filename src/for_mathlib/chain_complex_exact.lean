import algebra.homology.homology
import category_theory.abelian.exact
import category_theory.limits.shapes.zero_objects
import for_mathlib.complex_extend
import for_mathlib.homology_exact

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
  repeat {admit },
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

lemma exact_of_epi {𝒞 : Type*} [category 𝒞] [abelian 𝒞] {A B C : 𝒞} {f : A ⟶ B} {g : B ⟶ C}
  (hfg : f ≫ g = 0) [epi f] : exact f g :=
begin
  rw abelian.exact_iff,
  refine ⟨hfg, _⟩,
  rw [(abelian.epi_iff_cokernel_π_eq_zero _).1 (show epi f, from infer_instance), comp_zero],
end

lemma exact_zero_snd_iff_epi {𝒞 : Type*} [category 𝒞] [abelian 𝒞] {A B C : 𝒞}
  {f : A ⟶ B} : exact f (0 : B ⟶ C) ↔ epi f :=
begin
  split,
  { intro h,
    apply preadditive.epi_of_cokernel_zero,
    rcases (abelian.exact_iff _ _).1 h with ⟨-, h2⟩,
    simpa using h2, },
  { introI _,
    exact exact_of_epi comp_zero, },
end

lemma exact_of_mono {𝒞 : Type*} [category 𝒞] [abelian 𝒞] {A B C : 𝒞} {f : A ⟶ B} {g : B ⟶ C}
  (hfg : f ≫ g = 0) [mono g] : exact f g :=
begin
  rw abelian.exact_iff,
  refine ⟨hfg, _⟩,
  rw [(abelian.mono_iff_kernel_ι_eq_zero g).1 infer_instance, zero_comp],
end

lemma exact_zero_fst_iff_mono {𝒞 : Type*} [category 𝒞] [abelian 𝒞] {A B C : 𝒞}
  {g : B ⟶ C} : exact (0 : A ⟶ B) g ↔ mono g :=
begin
  split,
  { intro h,
    apply preadditive.mono_of_kernel_zero,
    rcases (abelian.exact_iff _ _).1 h with ⟨-, h2⟩,
    simpa using h2, },
  { introI _,
    exact exact_of_mono zero_comp, },
end

lemma nat_epi_iff_exact : epi (D.d 1 0) ↔
  exact (homological_complex.d_to D 0) (homological_complex.d_from D 0) :=
begin
  rw [homological_complex.d_to_eq _ (show (complex_shape.down ℕ).rel 1 0, by simp),
    exact_iso_comp],
  split,
  { introI h,
    apply exact_of_epi,
    simp only [homological_complex.d_from_eq_zero, next_nat_zero, comp_zero], },
  { intro h,
    simp only [homological_complex.d_from_eq_zero, next_nat_zero] at h,
    exact exact.epi_of_eq_zero h rfl, },
end

lemma nat_exact_iff_to_from_exact (i : ℕ) :
  exact (D.d (i + 2) (i + 1)) (D.d (i + 1) i) ↔
  exact (homological_complex.d_to D (i + 1)) (homological_complex.d_from D (i + 1)) :=
by rw [homological_complex.d_from_eq _ (show (complex_shape.down ℕ).rel i.succ i, by simp),
    exact_comp_iso, homological_complex.d_to_eq _ (show (complex_shape.down ℕ).rel
      i.succ.succ i.succ, by simp), exact_iso_comp ]

lemma is_zero_homology_of_epi_and_exact
  (h1 : epi (D.d 1 0))
  (h2 : ∀ i : ℕ, exact (D.d (i+2) (i+1)) (D.d (i+1) (i))) :
  ∀ i : ℤ, is_zero (((homological_complex.embed $
    complex_shape.embedding.nat_down_int_down).obj D).homology i) :=
begin
  intro i,
  rw category_theory.is_zero_homology_iff_exact,
  rcases lt_trichotomy i 0 with (hi | rfl | hi),
  { have : is_zero (((homological_complex.embed complex_shape.embedding.nat_down_int_down).obj D).X i),
    { delta homological_complex.embed homological_complex.embed.obj
        complex_shape.embedding.nat_down_int_down complex_shape.embedding.pos_int_to_onat,
      obtain ⟨j, rfl⟩ := int.eq_neg_succ_of_lt_zero hi,
      simp only [is_zero_zero A, homological_complex.embed.X_none],
    },
  exact category_theory.limits.is_zero.exact this _ _ },
  { rw [homological_complex.d_from_eq _ (show (complex_shape.down ℤ).rel 0 (-1), by simp),
    exact_comp_iso, homological_complex.d_to_eq _ (show (complex_shape.down ℤ).rel 1 0, by simp),
    exact_iso_comp],
    apply exact_of_epi (homological_complex.d_comp_d _ (1 : ℤ) 0 (-1)),
    exact h1 }, -- maybe defeq abuse?
  { obtain ⟨j, rfl⟩ := int.eq_succ_of_zero_lt hi, clear hi,
    specialize h2 j,
    rw [homological_complex.d_from_eq _ (show (complex_shape.down ℤ).rel (j.succ : ℕ) j, by simp),
    exact_comp_iso, homological_complex.d_to_eq _ (show (complex_shape.down ℤ).rel
      (j.succ.succ : ℕ) (j.succ), by simp),
    exact_iso_comp],
    exact h2 }, -- maybe defeq abuse
end

lemma epi_and_exact_iff_is_zero_homology :
  (epi (D.d 1 0) ∧ ∀ i : ℕ, exact (D.d (i+2) (i+1)) (D.d (i+1) (i))) ↔
  (∀ i : ℤ, is_zero (((homological_complex.embed $
    complex_shape.embedding.nat_down_int_down).obj D).homology i)) :=
⟨λ h, is_zero_homology_of_epi_and_exact D h.1 h.2,
  epi_and_exact_of_is_zero_homology _⟩

lemma homology_zero_iff_homology_zero :
  (∀ i : ℤ, is_zero (((homological_complex.embed $
    complex_shape.embedding.nat_down_int_down).obj D).homology i)) ↔
  (∀ i : ℕ, is_zero (D.homology i)) :=
begin
  rw ← epi_and_exact_iff_is_zero_homology,
  simp_rw [category_theory.is_zero_homology_iff_exact, nat_epi_iff_exact,
    nat_exact_iff_to_from_exact],
  split,
  { rintro ⟨h0, hS⟩ ( _ | i),
    { exact h0 },
    { exact hS i }, },
  { intro h,
    exact ⟨h 0, λ i, h i.succ⟩, },
end

universes v' u'

-- `kernel_comparison_comp_ι` in mathlib master (as I write) is not
-- maximally universe-polymorphic; the morphisms of both categories live in the
-- same universe. So we write `[category.{v} B]` instead of `[category.{v'} B]` here.

-- TODO : fix kernel_comparison_comp_ι (if this is indeed an oversight)

lemma exact_iff_map_exact {α : Type*} {c : complex_shape α}
  (D : homological_complex A c)
  {B : Type u'} [category.{v} B] [abelian B] (E : A ≌ B)
  [E.functor.additive] (i j k : α) (f : D.X i ⟶ D.X j) (g : D.X j ⟶ D.X k) :
  exact f g ↔ exact (E.functor.map f) (E.functor.map g) :=
begin
  rw abelian.exact_iff,
  rw abelian.exact_iff,
  apply and_congr,
   { rw [← functor.map_comp],
     exact (functor.map_eq_zero_iff _).symm, },
   { rw [← functor.map_eq_zero_iff E.functor, functor.map_comp],
     rw ← kernel_comparison_comp_ι,
     rw ← π_comp_cokernel_comparison,
     rw ← preserves_kernel.iso_hom,
     rw ← preserves_cokernel.iso_inv,
     rw category.assoc,
     rw preadditive.is_iso.comp_left_eq_zero,
     rw ← category.assoc,
     rw preadditive.is_iso.comp_right_eq_zero, }
end



-- morphisms of B in same universe as morphisms of A because of
-- `exact_iff_map_exact`
lemma homology_zero_iff_map_homology_zero
  {α : Type*} {c : complex_shape α}
  (D : homological_complex A c)
  {B : Type u'} [category.{v} B] [abelian B] (E : A ≌ B)
  [E.functor.additive] :
  (∀ i : α, is_zero (D.homology i)) ↔
  (∀ i : α, is_zero (((E.functor.map_homological_complex _).obj D).homology i)) :=
begin
  apply forall_congr,
  intro i,
  rw category_theory.is_zero_homology_iff_exact,
  rw category_theory.is_zero_homology_iff_exact,
  rw functor.map_homological_complex,
  dsimp only,
  rcases hnext : c.next i with _ | ⟨knext,wnext⟩;
  rcases hprev : c.prev i with _ | ⟨kprev,wprev⟩,
  { rw homological_complex.d_from_eq_zero _ hnext,
    rw homological_complex.d_from_eq_zero _ hnext,
    rw homological_complex.d_to_eq_zero _ hprev,
    rw homological_complex.d_to_eq_zero _ hprev,
    rw ← is_zero_iff_exact_zero_zero,
    rw ← is_zero_iff_exact_zero_zero,
    rw is_zero_iff_id_eq_zero,
    rw is_zero_iff_id_eq_zero,
    rw ← category_theory.functor.map_id,
    rw E.functor.map_eq_zero_iff,
  },
  { rw homological_complex.d_from_eq_zero _ hnext,
    rw homological_complex.d_from_eq_zero _ hnext,
    rw homological_complex.d_to_eq _ wprev,
    rw homological_complex.d_to_eq _ wprev,
    rw exact_iso_comp,
    rw exact_iso_comp,
    rw exact_zero_snd_iff_epi,
    rw exact_zero_snd_iff_epi,
    split,
    { introI _,
      exact category_theory.preserves_epi E.functor (D.d kprev i) },
    { introI _,
      exact reflects_epi E.functor (D.d kprev i), }, },
  {
    rw homological_complex.d_from_eq _ wnext,
    rw homological_complex.d_from_eq _ wnext,
    rw homological_complex.d_to_eq_zero _ hprev,
    rw homological_complex.d_to_eq_zero _ hprev,
    rw exact_comp_iso,
    rw exact_comp_iso,
    rw exact_zero_fst_iff_mono,
    rw exact_zero_fst_iff_mono,
    dsimp,
    split,
    { introI _,
      exact category_theory.preserves_mono E.functor (D.d i knext),
    },
    { introI _,
      exact reflects_mono E.functor (D.d i knext) }, },
  { rw homological_complex.d_to_eq _ wprev,
    rw homological_complex.d_to_eq _ wprev,
    rw homological_complex.d_from_eq _ wnext,
    rw homological_complex.d_from_eq _ wnext,
    rw exact_comp_iso,
    rw exact_comp_iso,
    rw exact_iso_comp,
    rw exact_iso_comp,
    apply exact_iff_map_exact, }
end

end chain_complex
