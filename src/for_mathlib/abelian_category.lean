import category_theory.preadditive


namespace category_theory

open category_theory.limits

variables {C : Type*} [category C] [preadditive C] [has_zero_object C]

structure is_zero (X : C) : Prop :=
(eq_zero_of_src : ∀ {Y : C} (f : X ⟶ Y), f = 0)
(eq_zero_of_tgt : Π {Y : C} (f : Y ⟶ X), f = 0)

open_locale zero_object

lemma is_zero_zero : is_zero (0 : C) :=
{ eq_zero_of_src := λ Y f, by ext,
  eq_zero_of_tgt := λ Y f, by ext }

end category_theory
