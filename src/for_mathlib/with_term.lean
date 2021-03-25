import category_theory.limits.shapes.terminal
import category_theory.limits.preserves.shapes.terminal
import category_theory.fin_category

namespace category_theory

universes v u

def with_term (C : Type u) [category.{v} C] := option C

namespace with_term

variables {C : Type u} [category.{v} C]

def star : with_term C := none

@[simp]
def hom : with_term C → with_term C → Type v
| (some X) (some Y) := X ⟶ Y
| none (some X) := pempty
| _ none := punit

@[simp]
def comp : Π {X Y Z : with_term C}, hom X Y → hom Y Z → hom X Z
| (some X) (some Y) (some Z) := λ f g, f ≫ g
| (some X) _ none := λ f g, punit.star
| none (some X) _ := λ f g, pempty.elim f
| _ none (some Y) := λ f g, pempty.elim g
| none none none := λ _ _, punit.star

@[simp]
def id : Π {X : with_term C}, hom X X
| (some X) := 𝟙 _
| none := punit.star

@[simps]
instance : category (with_term C) :=
{ hom := hom,
  id := λ X, id,
  comp := λ X Y Z, comp,
  id_comp' := by {rintro ⟨X|X⟩ ⟨Y|Y⟩, tidy},
  comp_id' := by {rintro ⟨X|X⟩ ⟨Y|Y⟩, tidy},
  assoc' := by {rintro ⟨X|X⟩ ⟨Y|Y⟩ ⟨Z|Z⟩ ⟨W|W⟩, tidy} }

instance {D : Type*} [small_category D] [fin_category D] :
  fin_category (with_term D) :=
{ fintype_obj := by {change fintype (option _), apply_instance},
  decidable_eq_hom := λ x y, begin
    cases x;
    cases y,
    any_goals {change (decidable_eq punit), apply_instance},
    any_goals {change (decidable_eq pempty), apply_instance},
    change decidable_eq (x ⟶ y), apply_instance,
  end,
  fintype_hom := λ X Y, begin
    cases X; cases Y,
    any_goals {change fintype pempty, apply_instance},
    any_goals {change fintype punit, apply_instance},
    change fintype (X ⟶ Y), apply_instance
  end }

@[simps]
def incl : C ⥤ with_term C :=
{ obj := some,
  map := λ _ _ f, f }

@[simp]
instance {X : with_term C} : unique (X ⟶ star) := by {rcases X, tidy}

@[simp]
instance : limits.has_terminal (with_term C) := limits.has_terminal_of_unique star

@[simps]
def is_terminal_star : limits.is_terminal (star : with_term C) :=
{ lift := λ S, option.rec_on S.X (𝟙 _) (λ x, punit.star),
  uniq' := by {rintro ⟨⟨X|X⟩,_⟩, tidy} }

@[simps]
noncomputable
def star_iso : star ≅ (⊤_ (with_term C)) :=
{ hom := limits.terminal.from _,
  inv := limits.is_terminal.from is_terminal_star _ }

@[simp]
noncomputable
def lift {D : Type*} [category D] [limits.has_terminal D] (F : C ⥤ D) : (with_term C) ⥤ D :=
{ obj := λ X, option.rec_on X (⊤_ _) F.obj,
  map := λ X Y, option.rec_on Y (λ f, limits.terminal.from _)
    (λ y, option.rec_on X (λ f, pempty.elim f) (λ x f, F.map f)),
  map_id' := by {rintro ⟨X|X⟩, tidy},
  map_comp' := by {rintro ⟨X|X⟩ ⟨Y|Y⟩ ⟨Z|Z⟩, tidy} }

@[simps]
noncomputable
instance {D : Type*} [category D] [limits.has_terminal D] {F : C ⥤ D} :
  limits.preserves_limit (functor.empty _) (lift F) :=
limits.preserves_terminal_of_iso _ $ ((lift F).map_iso star_iso).symm ≪≫
{ hom := 𝟙 _,
  inv := 𝟙 _ }.

@[simps]
noncomputable
def lift_comp_incl {D : Type*} [category D] [limits.has_terminal D] {F : C ⥤ D} :
  incl ⋙ (lift F) ≅ F :=
{ hom := { app := λ X, 𝟙 _ },
  inv := { app := λ X, 𝟙 _ }, }.

@[simps]
noncomputable
def lift_unique {D : Type*} [category D] [limits.has_terminal D] {F : C ⥤ D}
  {G : with_term C ⥤ D} [limits.preserves_limit (functor.empty _) G]
  (cond : incl ⋙ G ≅ F) : G ≅ lift F :=
{ hom :=
  { app := λ X, option.rec_on X (limits.terminal.from _) cond.hom.app,
    naturality' := begin
      rintro ⟨X|X⟩ ⟨Y|Y⟩,
      swap 4,
      intros f,
      erw ← cond.hom.naturality,
      tidy
    end },
  inv :=
  { app := λ X, option.rec_on X (
      let AA := (G.map_iso star_iso).symm.hom,
          BB := (limits.preserves_terminal.iso G).symm.hom in
      limits.terminal.from _ ≫ BB ≫ AA ) $ λ x, cond.symm.hom.app x,
    naturality' := begin
      dsimp,
      rintro ⟨X|X⟩ ⟨Y|Y⟩,
      any_goals { intro f,
        apply limits.is_terminal.hom_ext,
        apply limits.is_terminal_obj_of_is_terminal,
        exact is_terminal_star },
      { intro f, exact pempty.elim f },
      { intro f,
        dsimp,
        erw ← cond.symm.hom.naturality,
        refl },
    end },
  hom_inv_id' := begin
    ext ⟨X|X⟩,
    swap 2, {tidy},
    apply limits.is_terminal.hom_ext,
    apply limits.is_terminal_obj_of_is_terminal,
    exact is_terminal_star
  end,
  inv_hom_id' := by {ext ⟨X|X⟩, tidy} }

end with_term

end category_theory
