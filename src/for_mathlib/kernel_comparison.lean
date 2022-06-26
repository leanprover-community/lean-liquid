import category_theory.limits.shapes.kernels

open category_theory

universes v
namespace category_theory.limits

variables {C D : Type*} [category.{v} C] [category.{v} D]
  [has_zero_morphisms C] [has_zero_morphisms D]

@[simp, reassoc]
lemma lift_map_inv_kernel_comparison {X Y Z : C} (f : Y ⟶ Z) [has_kernel f] (G : C ⥤ D)
  [G.preserves_zero_morphisms] [has_kernel (G.map f)] [is_iso (kernel_comparison f G)]
  {g : X ⟶ Y} (w : g ≫ f = 0) :
  kernel.lift (G.map f) (G.map g) (by simp only [← G.map_comp, w, functor.map_zero]) ≫
  category_theory.inv (kernel_comparison f G) = G.map (kernel.lift f g w) :=
by simp [← cancel_mono (kernel_comparison f G)]

@[simp, reassoc]
lemma inv_cokernel_comparison_desc_map {X Y Z : C} (f : X ⟶ Y) [has_cokernel f] (G : C ⥤ D)
  [G.preserves_zero_morphisms] [has_cokernel (G.map f)] [is_iso (cokernel_comparison f G)]
  {g : Y ⟶ Z} (w : f ≫ g = 0) :
  category_theory.inv (cokernel_comparison f G) ≫
    cokernel.desc (G.map f) (G.map g) (by simp only [← G.map_comp, w, functor.map_zero]) =
  G.map (cokernel.desc f g w) :=
by simp [← cancel_epi (cokernel_comparison f G)]

end category_theory.limits
