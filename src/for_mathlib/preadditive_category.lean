import category_theory.abelian.additive_functor -- minimize this

namespace category_theory

namespace preadditive

open limits

variables {C D : Type*} [category C] [category D] [preadditive C] {X Y Z : C}

def comp_hom : (X ⟶ Y) →+ (Y ⟶ Z) →+ (X ⟶ Z) :=
add_monoid_hom.mk' (λ f, left_comp _ f) $
  λ f₁ f₂, add_monoid_hom.ext $ λ g, (right_comp _ g).map_add f₁ f₂

instance : preadditive (D ⥤ C) :=
{ hom_group := λ F G,
  { add := λ α β,
    { app := λ X, α.app X + β.app X,
      naturality' := by { intros, rw [comp_add, add_comp, α.naturality, β.naturality] } },
    zero := { app := λ X, 0, naturality' := by { intros, rw [zero_comp, comp_zero] } },
    neg := λ α,
    { app := λ X, -α.app X,
      naturality' := by { intros, rw [comp_neg, neg_comp, α.naturality] } },
    sub := λ α β,
    { app := λ X, α.app X - β.app X,
      naturality' := by { intros, rw [comp_sub, sub_comp, α.naturality, β.naturality] } },
    add_assoc := by { intros, ext, apply add_assoc },
    zero_add := by { intros, ext, apply zero_add },
    add_zero := by { intros, ext, apply add_zero },
    sub_eq_add_neg := by { intros, ext, apply sub_eq_add_neg },
    add_left_neg := by { intros, ext, apply add_left_neg },
    add_comm := by { intros, ext, apply add_comm } },
  add_comp' := by { intros, ext, apply add_comp },
  comp_add' := by { intros, ext, apply comp_add } }

end preadditive

end category_theory
