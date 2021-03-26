import category_theory.limits.cones

namespace category_theory

universes v v₁ u

variables (α γ : Type v) {β : Type v₁}

inductive fan : Type v
| right : fan
| left : α → fan

namespace fan

local attribute [tidy] tactic.case_bash

variables {α γ}

inductive hom : Π (X Y : fan α), Type v
| id : Π X : fan α, hom X X
| of : Π (a : α), hom (left a) right

instance : small_category (fan α) :=
{ hom := hom,
  id := λ X, hom.id _,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _, _, (hom.id _), h := h
  | _, _, right, (hom.of a), h := hom.of a
  end }.

def map (f : α → β) : fan α ⥤ fan β :=
{ obj := λ X,
    match X with
    | right := right
    | left a := left (f a)
    end,
  map := λ X Y g,
    match X, Y, g with
    | _, _, (hom.id _) := hom.id _
    | _, _, (hom.of a) := hom.of (f a)
    end }.

@[simps]
def mk {D : Type u} [category.{v} D] {B : D} (X : α → D) (F : Π a, X a ⟶ B) :
  fan α ⥤ D :=
{ obj := λ i,
    match i with
    | right := B
    | left j := X j
    end,
  map := λ i j m,
    match i, j, m with
    | _, _, hom.id _ := 𝟙 _
    | _, _, hom.of _ := F _
    end }

def map_cone (f : α → γ) {D : Type u} [category.{v} D] {B : D}
  (X : γ → D) (F : Π a, X a ⟶ B) (C : limits.cone (mk X F)) : limits.cone (mk (X ∘ f) (λ i, F (f i))) :=
{ X := C.X,
  π :=
  { app := λ i,
      match i with
      | right := C.π.app right
      | left j := C.π.app (left _)
      end,
    naturality' := begin
      intros x y m,
      cases x; cases y; cases m,
      any_goals {erw [category.id_comp, category.comp_id]},
      erw [category.id_comp],
      have := C.π.naturality (hom.of (f x)),
      erw [← this, category.id_comp],
      refl,
    end } }

end fan

end category_theory
