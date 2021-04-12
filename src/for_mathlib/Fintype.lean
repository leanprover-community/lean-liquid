import category_theory.Fintype

namespace Fintype

@[simp]
lemma id_apply {A : Fintype} (a : A) : (𝟙 A : A → A) a = a := rfl

@[simp]
lemma comp_apply {A B C : Fintype} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
  (f ≫ g) a = g (f a) := rfl

end Fintype
