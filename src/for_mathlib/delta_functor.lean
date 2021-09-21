import category_theory.preadditive
import category_theory.abelian.projective

import for_mathlib.abelian_category

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables (𝒞 : Type u) [category.{v} 𝒞] [has_images 𝒞] [has_zero_morphisms 𝒞] [has_kernels 𝒞]

@[ext]
structure short_exact_sequence :=
(fst snd trd : 𝒞)
(f : fst ⟶ snd)
(g : snd ⟶ trd)
(mono : mono f)
(epi : epi g)
(exact : exact f g)

variables {𝒞}

namespace short_exact_sequence

@[ext]
structure hom (A B : short_exact_sequence 𝒞) :=
(fst : A.1 ⟶ B.1)
(snd : A.2 ⟶ B.2)
(trd : A.3 ⟶ B.3)
(sq1' : fst ≫ B.f = A.f ≫ snd . obviously)
(sq2' : snd ≫ B.g = A.g ≫ trd . obviously)

namespace hom

restate_axiom sq1' sq1
restate_axiom sq2' sq2

attribute [reassoc] sq1 sq2

end hom

instance : quiver (short_exact_sequence 𝒞) := ⟨hom⟩

@[simps]
def id (A : short_exact_sequence 𝒞) : A ⟶ A :=
{ fst := 𝟙 _,
  snd := 𝟙 _,
  trd := 𝟙 _,
  sq1' := by simp only [category.id_comp, category.comp_id],
  sq2' := by simp only [category.id_comp, category.comp_id], }

@[simps]
def comp {A B C : short_exact_sequence 𝒞} (f : A ⟶ B) (g : B ⟶ C) : A ⟶ C :=
{ fst := f.1 ≫ g.1,
  snd := f.2 ≫ g.2,
  trd := f.3 ≫ g.3,
  sq1' := by rw [category.assoc, hom.sq1, hom.sq1_assoc],
  sq2' := by rw [category.assoc, hom.sq2, hom.sq2_assoc], }

instance : category (short_exact_sequence 𝒞) :=
{ id := id,
  comp := λ A B C f g, comp f g,
  id_comp' := by { intros, ext; dsimp; simp only [category.id_comp], },
  comp_id' := by { intros, ext; dsimp; simp only [category.comp_id], },
  assoc' := by { intros, ext; dsimp; simp only [category.assoc], },
  .. (infer_instance : quiver (short_exact_sequence 𝒞)) }

variables (𝒞)

@[simps] def Fst : short_exact_sequence 𝒞 ⥤ 𝒞 :=
{ obj := fst, map := λ A B f, f.1 }

@[simps] def Snd : short_exact_sequence 𝒞 ⥤ 𝒞 :=
{ obj := snd, map := λ A B f, f.2 }

@[simps] def Trd : short_exact_sequence 𝒞 ⥤ 𝒞 :=
{ obj := trd, map := λ A B f, f.3 }

end short_exact_sequence

variables {C : Type u} [category.{v} C] {D : Type*} [category D]

variables [has_images C] [has_zero_morphisms C] [has_kernels C]
variables [has_images D] [has_zero_morphisms D] [has_kernels D]

/-- Cohomological covariant delta functor. -/
class delta_functor (F : ℕ → C ⥤ D) :=
(δ : Π (n : ℕ), short_exact_sequence.Trd C ⋙ (F n) ⟶ short_exact_sequence.Fst C ⋙ (F (n+1)))
(mono : ∀ (A : short_exact_sequence C), mono ((F 0).map A.f))
(exact' : ∀ (n : ℕ) (A : short_exact_sequence C), exact ((F n).map A.f) ((F n).map A.g))
(exact_δ : ∀ (n : ℕ) (A : short_exact_sequence C), exact ((F n).map A.g) ((δ n).app A))
(δ_exact : ∀ (n : ℕ) (A : short_exact_sequence C), exact ((δ n).app A) ((F (n+1)).map A.f))

namespace delta_functor

variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]
variables (F : ℕ → C ⥤ 𝒜) [delta_functor F]

example (A : short_exact_sequence C)
  (hA₂ : ∀ i, 0 < i → is_zero ((F i).obj A.2)) (hA₃ : ∀ i, 0 < i → is_zero ((F i).obj A.3))
  (i : ℕ) (hi : 1 < i) :
  is_zero ((F i).obj A.1) :=
begin
  obtain ⟨i, rfl⟩ : ∃ k, i = k + 2, { simpa only [add_comm] using nat.exists_eq_add_of_le hi },
  refine is_zero_of_exact_zero_zero' _ _ (delta_functor.δ_exact (i+1) A) _ _,
  { exact (hA₃ (i+1) i.succ_pos).eq_zero_of_src _ },
  { refine (hA₂ (i+2) _).eq_zero_of_tgt _, exact pos_of_gt hi }
end

end delta_functor

end category_theory
