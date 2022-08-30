import for_mathlib.short_complex_functor_category

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace category_theory

namespace functor

variables {C₁ C₂ C₃ : Type*} [category C₁] [category C₂] [category C₃] [has_zero_morphisms C₃]
  [has_zero_object C₃]

lemma is_zero_of_comp (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (h : limits.is_zero G) :
  limits.is_zero (F ⋙ G) :=
begin
  rw limits.is_zero.iff_id_eq_zero,
  ext,
  apply limits.is_zero.eq_zero_of_src,
  dsimp,
  apply limits.is_zero.obj,
  exact h,
end

end functor

end category_theory

namespace homological_complex

variables (C : Type*) [category C] [has_zero_morphisms C] [has_zero_object C]
  {M : Type*} (c : complex_shape M)

@[simps]
def prev_functor (i : M) : homological_complex C c ⥤ C :=
homological_complex.eval _ c (c.prev i)

@[simps]
def next_functor (i : M) : homological_complex C c ⥤ C :=
homological_complex.eval _ c (c.next i)

def prev_functor_iso_eval (i j : M) (hij : c.rel j i) :
  prev_functor C c i ≅ homological_complex.eval C c j :=
nat_iso.of_components
  (λ X, X.X_prev_iso hij)
  (λ X Y f, by { dsimp, rw [← iso.eq_comp_inv, assoc, ← hom.prev_eq f hij], })

def next_functor_iso_eval (i j : M) (hij : c.rel i j) :
  next_functor C c i ≅ homological_complex.eval C c j :=
nat_iso.of_components
  (λ X, X.X_next_iso hij)
  (λ X Y f, by { dsimp, rw [← iso.eq_comp_inv, assoc, ← hom.next_eq f hij], })

end homological_complex

namespace short_complex

variables (C : Type*) [category C] [has_zero_morphisms C] [has_zero_object C]
  {M : Type*} (c : complex_shape M)

def functor_homological_complex_π₁_iso_prev_functor (i : M) :
  functor_homological_complex C c i ⋙ π₁ ≅ homological_complex.prev_functor C c i := by refl

def functor_homological_complex_π₂_iso_eval (i : M) :
  functor_homological_complex C c i ⋙ π₂ ≅ homological_complex.eval C c i := by refl

def functor_homological_complex_π₃_iso_next_functor (i : M) :
  functor_homological_complex C c i ⋙ π₃ ≅ homological_complex.next_functor C c i := by refl

end short_complex
