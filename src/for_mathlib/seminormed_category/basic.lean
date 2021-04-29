import category_theory.preadditive
import analysis.normed_space.basic

namespace category_theory

universes v u

old_structure_cmd

class semi_normed_category (C : Type u) [category.{v} C] :=
(hom_semi_normed_group : Π (X Y : C), semi_normed_group (X ⟶ Y) . tactic.apply_instance)
(add_comp' : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R),
  (f + f') ≫ g = f ≫ g + f' ≫ g . obviously)
(comp_add' : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R),
  f ≫ (g + g') = f ≫ g + f ≫ g' . obviously)
(norm_comp : ∀ (P Q R : C) (f : P ⟶ Q) (g : Q ⟶ R), ∥ f ≫ g ∥ ≤ ∥ f ∥ * ∥ g ∥)
(norm_id : ∀ (X : C), ∥ 𝟙 X ∥ = 1)

attribute [instance] semi_normed_category.hom_semi_normed_group
restate_axiom semi_normed_category.add_comp'
restate_axiom semi_normed_category.comp_add'
attribute [simp,reassoc] semi_normed_category.add_comp
attribute [simp, reassoc] semi_normed_category.comp_add
attribute [simp] semi_normed_category.norm_id

instance preadditive_of_semi_normed {C : Type*} [category C] [semi_normed_category C] :
  preadditive C := {} -- :-)

end category_theory
