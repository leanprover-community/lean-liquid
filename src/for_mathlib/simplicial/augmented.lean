import order.omega_complete_partial_order -- for preorder_hom.const
import algebraic_topology.simplicial_object

open opposite category_theory category_theory.limits
open simplex_category

universes v u

namespace category_theory

namespace simplex_category

lemma hom_zero_zero (f : mk 0 ⟶ mk 0) : f = 𝟙 _ :=
by { ext : 2, dsimp, exact subsingleton.elim _ _ }

end simplex_category

namespace cosimplicial_object

variables {C : Type u} [category.{v} C]

@[simps]
def augment (X₀ : C) (X : cosimplicial_object C) (f : X₀ ⟶ X.obj (mk 0))
  (hf : ∀ (n : simplex_category) (g₁ g₂ : mk 0 ⟶ n), f ≫ X.map g₁ = f ≫ X.map g₂) :
  augmented C :=
{ left := X₀,
  right := X,
  hom :=
  { app := λ n, f ≫ X.map (hom.mk $ preorder_hom.const _ 0),
    naturality' :=
    begin
      intros n₁ n₂ g,
      dsimp,
      simpa only [category.id_comp, category.assoc, ← X.map_comp] using hf _ _ _,
    end } }
.

@[simp] lemma augment_hom_zero (X₀ : C) (X : cosimplicial_object C) (f : X₀ ⟶ X.obj (mk 0)) (hf) :
  (X.augment X₀ f hf).hom.app (mk 0) = f :=
by { dsimp, rw [simplex_category.hom_zero_zero (@hom.mk _ _ _), X.map_id, category.comp_id] }

end cosimplicial_object
end category_theory
