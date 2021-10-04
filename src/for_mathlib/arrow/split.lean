import generalisation_linter
import category_theory.arrow

namespace category_theory
namespace arrow

universes v u

variables {C : Type u} [category.{v} C]

/-- Split arrows. -/
class split (f : arrow C) :=
(σ : f.right ⟶ f.left)
(is_splitting' : σ ≫ f.hom = 𝟙 _ . obviously)

restate_axiom split.is_splitting'
attribute [simp, reassoc] split.is_splitting

end arrow
end category_theory
#lint only generalisation_linter
