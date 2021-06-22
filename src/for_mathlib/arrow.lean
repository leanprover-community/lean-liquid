import category_theory.arrow
import category_theory.limits.has_limits

namespace category_theory

namespace arrow

universes v u

variables {C : Type u} [category.{v} C]

-- the rest of this file is mathlib PR: #7457

instance {f g : arrow C} (ff : f ⟶ g) [is_iso ff.left] [is_iso ff.right] :
  is_iso ff :=
{ out := ⟨⟨inv ff.left, inv ff.right⟩,
          by { ext; dsimp; simp only [is_iso.hom_inv_id] },
          by { ext; dsimp; simp only [is_iso.inv_hom_id] }⟩ }

end arrow

end category_theory
