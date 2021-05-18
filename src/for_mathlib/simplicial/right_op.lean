import algebraic_topology.simplicial_object

open opposite


namespace category_theory

universes v u₁ u₂

variables {C : Type u₁} [category.{v} C]

namespace simplicial_object

namespace augmented

variable (X : simplicial_object.augmented C)

-- TODO: Generalize and move!
@[simps]
def right_op : cosimplicial_object.augmented Cᵒᵖ :=
{ left := op $ point.obj X,
  right := (drop.obj X).right_op,
  hom := X.hom.right_op }

-- TODO: Generalize and move!
def right_op_functor : (simplicial_object.augmented C)ᵒᵖ ⥤
  (cosimplicial_object.augmented Cᵒᵖ) :=
{ obj := λ X, X.unop.right_op,
  map := λ X Y f,
  { left := (point.map f.unop).op,
    right := (drop.map f.unop).right_op,
    w' := begin
      ext,
      dsimp,
      simp_rw ← op_comp,
      congr' 1,
      have := f.unop.w,
      dsimp at this,
      apply_fun (λ η, η.app (op x)) at this,
      exact this.symm,
    end
    } }

end augmented

end simplicial_object

namespace cosimplicial_object

namespace augmented

variables {D : Type u₂} [category.{v} D] (F : C ⥤ D)

-- TODO: Generalize and move!
def map : augmented C ⥤ augmented D :=
{ obj := λ X,
  { left := F.obj X.left,
    right := X.right ⋙ F,
    hom := (functor.const_comp _ _ _).inv ≫ whisker_right X.hom F },
  map := λ X Y f,
  { left := F.map f.left,
    right := whisker_right f.right _,
    w' := sorry },
  map_id' := sorry,
  map_comp' := sorry
  }

end augmented

end cosimplicial_object

end category_theory
