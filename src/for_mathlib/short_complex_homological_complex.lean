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
{ obj := λ X, X.X_prev i,
  map := λ X Y f, f.prev i,
  map_id' := λ X, begin
    rcases h : c.prev i with _ | ⟨j, hij⟩,
    { apply is_zero.eq_of_src,
      exact is_zero.of_iso (limits.is_zero_zero C) (X.X_prev_iso_zero h), },
    { simp only [hom.prev_eq _ hij, id_f, id_comp, iso.hom_inv_id], },
  end,
  map_comp' := λ X Y W f g, begin
    rcases h : c.prev i with _ | ⟨j, hij⟩,
    { apply is_zero.eq_of_src,
      exact is_zero.of_iso (limits.is_zero_zero C) (X.X_prev_iso_zero h), },
    { simp only [hom.prev_eq _ hij, comp_f, assoc, iso.inv_hom_id_assoc, eq_self_iff_true], },
  end, }

@[simps]
def next_functor (i : M) : homological_complex C c ⥤ C :=
{ obj := λ X, X.X_next i,
  map := λ X Y f, f.next i,
  map_id' := λ X, begin
    rcases h : c.next i with _ | ⟨j, hij⟩,
    { apply is_zero.eq_of_src,
      exact is_zero.of_iso (limits.is_zero_zero C) (X.X_next_iso_zero h), },
    { simp only [hom.next_eq _ hij, id_f, id_comp, iso.hom_inv_id], },
  end,
  map_comp' := λ X Y W f g, begin
    rcases h : c.next i with _ | ⟨j, hij⟩,
    { apply is_zero.eq_of_src,
      exact is_zero.of_iso (limits.is_zero_zero C) (X.X_next_iso_zero h), },
    { simp only [hom.next_eq _ hij, comp_f, assoc, iso.inv_hom_id_assoc, eq_self_iff_true], },
  end, }

def prev_functor_is_zero (i : M) (h : c.prev i = none) : is_zero (prev_functor C c i) :=
begin
  rw is_zero.iff_id_eq_zero,
  ext X,
  apply is_zero.eq_of_src,
  exact is_zero.of_iso (limits.is_zero_zero C) (X.X_prev_iso_zero h),
end

def next_functor_is_zero (i : M) (h : c.next i = none) : is_zero (next_functor C c i) :=
begin
  rw is_zero.iff_id_eq_zero,
  ext X,
  apply is_zero.eq_of_src,
  exact is_zero.of_iso (limits.is_zero_zero C) (X.X_next_iso_zero h),
end

def prev_functor_iso_eval (i j : M) (hij : c.rel j i) :
  prev_functor C c i ≅ homological_complex.eval C c j :=
nat_iso.of_components
  (λ X, X.X_prev_iso hij)
  (λ X Y f, by { dsimp, simp only [hom.prev_eq f hij, assoc, iso.inv_hom_id, comp_id], })

def next_functor_iso_eval (i j : M) (hij : c.rel i j) :
  next_functor C c i ≅ homological_complex.eval C c j :=
nat_iso.of_components
  (λ X, X.X_next_iso hij)
  (λ X Y f, by { dsimp, simp only [hom.next_eq f hij, assoc, iso.inv_hom_id, comp_id], })

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
