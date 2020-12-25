import category_theory.functor_category
import category_theory.yoneda

namespace category_theory

namespace functor

universe variables v₁ v₂ v₃ u₁ u₂ u₃

variables {C : Type u₁} {D : Type u₂} {E : Type u₃}
variables [category.{v₁} C] [category.{v₂} D] [category.{v₃} E]

@[simps]
def uncurry (F : C ⥤ D ⥤ E) : C × D ⥤ E :=
{ obj := λ X, (F.obj X.1).obj X.2,
  map := λ X Y f, (F.obj X.1).map f.2 ≫ (F.map f.1).app Y.2 }

@[simps]
def curry (F : C × D ⥤ E) : C ⥤ D ⥤ E :=
{ obj := λ X,
  { obj := λ Y, F.obj (X, Y),
    map := λ Y₁ Y₂ g, F.map (𝟙 _, g),
    map_id' := λ Y, F.map_id _,
    map_comp' := by { intros, rw ← F.map_comp, dsimp, rw category.comp_id } },
  map := λ X₁ X₂ f,
  { app := λ Y, F.map (f, 𝟙 _),
    naturality' := by { intros, dsimp, simp only [← F.map_comp], dsimp,
      simp only [category.comp_id, category.id_comp] } },
  map_id' := λ X, by { dsimp, ext, dsimp, exact F.map_id _ },
  map_comp' := by { intros, dsimp, ext, dsimp, rw ← F.map_comp, dsimp, rw category.comp_id } }

end functor

end category_theory
