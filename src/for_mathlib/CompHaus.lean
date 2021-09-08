import topology.category.CompHaus

namespace CompHaus

open category_theory

noncomputable instance : limits.preserves_limits (forget CompHaus) :=
by apply limits.comp_preserves_limits CompHaus_to_Top (forget Top)

@[simp] lemma coe_id (X : CompHaus) : (𝟙 X : X → X) = id := rfl
@[simp] lemma coe_comp {A B C : CompHaus} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g : A → C) = g ∘ f := rfl

lemma coe_id_apply {X : CompHaus} (x : X) : (𝟙 X : X → X) x = x := by simp
lemma coe_comp_apply {X Y Z : CompHaus} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := by simp

end CompHaus
