import tactic
import category_theory.yoneda

namespace category_theory

universes w v u
variables {C : Type u} [category.{v} C]

@[simps]
def yoneda' : C ⥤ Cᵒᵖ ⥤ Type (max w v) :=
{ obj := λ X, yoneda.obj X ⋙ ulift_functor.{w},
  map := λ X Y f, whisker_right (yoneda.map f) _,
  map_id' := λ X, by { erw [functor.map_id, whisker_right_id], refl },
  map_comp' := λ X Y Z f g, by { rw [functor.map_comp, whisker_right_comp] } }

open opposite

@[simps]
def yoneda'_equiv (X : C) (F : Cᵒᵖ ⥤ Type (max w v)) :
  (yoneda'.{w}.obj X ⟶ F) ≃ F.obj (op X) :=
{ to_fun := λ e, e.app _ ⟨𝟙 _⟩,
  inv_fun := λ t, { app := λ Y f, F.map f.down.op t },
  left_inv := begin
    intros f,
    ext Y ⟨t⟩,
    have := (f.naturality t.op).symm,
    apply_fun (λ e, e ⟨𝟙 _⟩) at this,
    dsimp at t ⊢ this,
    rw [this, category.comp_id],
  end,
  right_inv := by tidy }

end category_theory
