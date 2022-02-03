import category_theory.abelian.basic

namespace category_theory

variables (C : Type*) [category C]

/-- `endomorphism C` is the category endomorphisms in `C`.
In other words, the objects are pairs `(X, f)`, with `X : C` and `f : X ⟶ X`,
and morphisms are morphisms from `C` that commute with the distinguished endomorphisms. -/
structure endomorphism :=
(X : C)
(f : X ⟶ X)

namespace endomorphism

@[ext] structure hom {C : Type*} [category C] (X Y : endomorphism C) :=
(f : X.X ⟶ Y.X)
(comm : X.f ≫ f = f ≫ Y.f)

attribute [reassoc] hom.comm

instance : category_struct (endomorphism C) :=
{ hom := λ X Y, hom X Y,
  id := λ X, ⟨𝟙 X.X, by rw [category.id_comp, category.comp_id]⟩,
  comp := λ X Y Z f g, ⟨f.1 ≫ g.1, by rw [hom.comm_assoc, hom.comm, category.assoc]⟩ }

variables {C} {X Y Z : endomorphism C} (f : X ⟶ Y) (g : Y ⟶ Z)

@[simp] lemma id_f (X : endomorphism C) : hom.f (𝟙 X) = 𝟙 X.X := rfl

@[simp] lemma comp_f : (f ≫ g).f = f.f ≫ g.f := rfl

@[reassoc] lemma hom_comm : X.f ≫ f.f = f.f ≫ Y.f := f.comm

instance : category (endomorphism C) :=
{ comp_id' := by { intros, ext, exact category.comp_id _ },
  id_comp' := by { intros, ext, exact category.id_comp _ },
  assoc' := by { intros, ext, exact category.assoc _ _ _ },
  ..(_ : category_struct (endomorphism C)) }

instance [abelian C] : abelian (endomorphism C) :=
sorry

end endomorphism

end category_theory
