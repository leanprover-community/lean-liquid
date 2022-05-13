import category_theory.preadditive.additive_functor

import for_mathlib.free_abelian_group

noncomputable theory

universes v u

namespace category_theory

structure FreeAb (C : Type u) [category.{v} C] := of ::
(as : C)

namespace FreeAb

variables (C : Type u) [category.{v} C]

instance : quiver (FreeAb C) :=
{ hom := λ X Y, free_abelian_group (X.as ⟶ Y.as) }

variables {C}

protected def id (X : FreeAb C) : X ⟶ X := free_abelian_group.of (𝟙 X.as)

protected def comp {X Y Z : FreeAb C} : (X ⟶ Y) →+ (Y ⟶ Z) →+ (X ⟶ Z) :=
free_abelian_group.lift $ λ f : X.as ⟶ Y.as,
  free_abelian_group.lift $ λ g : Y.as ⟶ Z.as, free_abelian_group.of (f ≫ g)

variables (C)

instance : category_struct (FreeAb C) :=
{ id := FreeAb.id,
  comp := λ X Y Z f g, FreeAb.comp f g }

@[simp]
protected lemma comp_apply {X Y Z : FreeAb C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  FreeAb.comp f g = f ≫ g := rfl

instance : category (FreeAb C) :=
{ id_comp' := λ X Y f, begin
    show FreeAb.comp X.id f = add_monoid_hom.id _ f, congr' 1, clear f, ext1 f,
    simp only [add_monoid_hom.id_apply, FreeAb.comp, free_abelian_group.lift.of, FreeAb.id,
      category.id_comp],
  end,
  comp_id' := λ X Y f, begin
    show FreeAb.comp f Y.id = add_monoid_hom.id _ f,
    rw [← add_monoid_hom.flip_apply], congr' 1, clear f, ext1 f,
    simp only [add_monoid_hom.id_apply, FreeAb.comp, free_abelian_group.lift.of, FreeAb.id,
      category.comp_id, add_monoid_hom.flip_apply],
  end,
  assoc' := λ W X Y Z f g h, begin
    show FreeAb.comp.comp (FreeAb.comp f) g h = (FreeAb.comp f).comp (FreeAb.comp g) h,
    congr' 1,
    rw [← add_monoid_hom.comp_hom_apply_apply, ← add_monoid_hom.comp_hom_apply_apply,
        ← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_apply],
    congr' 1,
    conv_rhs { rw [← add_monoid_hom.comp_hom_apply_apply, ← add_monoid_hom.flip_apply,
      ← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_apply] },
    congr' 1,
    clear f g h, ext f g h,
    simp only [add_monoid_hom.comp_apply, add_monoid_hom.comp_hom_apply_apply,
      add_monoid_hom.flip_apply, FreeAb.comp, free_abelian_group.lift.of, category.assoc],
  end }
.

instance : preadditive (FreeAb C) :=
{ hom_group := by { intros, apply_instance },
  add_comp' := by { intros, show FreeAb.comp (_ + _) _ = _, simp only [map_add], refl },
  comp_add' := by { intros, show FreeAb.comp _ (_ + _) = _, simp only [map_add], refl } }

def eval [preadditive C] : FreeAb C ⥤ C :=
{ obj := FreeAb.as,
  map := λ X Y, free_abelian_group.lift id,
  map_id' := λ X, show free_abelian_group.lift id X.id = 𝟙 X.as,
    by { simp only [FreeAb.id, free_abelian_group.lift.of], refl },
  map_comp' := λ X Y Z f g, begin
    show free_abelian_group.lift id (FreeAb.comp f g) = preadditive.comp_hom _ _,
    rw [← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_apply], congr' 1,
    rw [← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_hom_apply_apply,
        ← add_monoid_hom.comp_apply],
    conv_rhs { rw [← add_monoid_hom.comp_hom_apply_apply, ← add_monoid_hom.flip_apply,
      ← add_monoid_hom.comp_apply] }, congr' 1, clear f g, ext f g,
    simp only [add_monoid_hom.comp_apply, add_monoid_hom.comp_hom_apply_apply,
      add_monoid_hom.flip_apply, FreeAb.comp, free_abelian_group.lift.of],
    refl,
  end }

end FreeAb

namespace functor

variables {C D : Type*} [category C] [category D]

def map_FreeAb (F : C ⥤ D) : FreeAb C ⥤ FreeAb D :=
{ obj := λ X, FreeAb.of (F.obj X.as),
  map := λ X Y, free_abelian_group.map (λ f, F.map f),
  map_id' := λ X, by { erw [free_abelian_group.map_of_apply, F.map_id], refl },
  map_comp' := λ X Y Z f g, begin
    rw [← FreeAb.comp_apply, ← FreeAb.comp_apply,
        ← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_apply], congr' 1,
    rw [← add_monoid_hom.comp_hom_apply_apply, ← add_monoid_hom.comp_apply],
    conv_rhs { rw [← add_monoid_hom.comp_hom_apply_apply, ← add_monoid_hom.flip_apply,
      ← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_apply] }, congr' 1, clear f g, ext f g,
    simp only [add_monoid_hom.comp_apply, add_monoid_hom.comp_hom_apply_apply,
      add_monoid_hom.flip_apply, FreeAb.comp, free_abelian_group.lift.of,
      free_abelian_group.map, ← F.map_comp],
  end }

end functor

end category_theory
