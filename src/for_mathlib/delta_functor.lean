import for_mathlib.short_exact_sequence

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables (𝒞 : Type u) [category.{v} 𝒞]
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
  { exact (hA₃ (i+1) i.succ_pos).eq_of_src _ _ },
  { refine (hA₂ (i+2) _).eq_of_tgt _ _, exact pos_of_gt hi }
end

end delta_functor

end category_theory
