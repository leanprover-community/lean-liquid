import category_theory.limits.preserves.basic
import category_theory.limits.concrete_category

namespace category_theory

namespace concrete_category

universes v u
variables {C : Type u} [category.{v} C] [concrete_category.{v} C]
  {J : Type v} [small_category J] (G : J ⥤ C) [limits.has_limit G]
  [limits.preserves_limit G (forget C)]

local attribute [instance] has_coe_to_sort has_coe_to_fun

/-- If `C` is a concrete category for which the forgetful functor
preserves limits, then the type `limit G` is in bijection with the type of
sequences compatible with the transition morphisms in the diagram. -/
noncomputable def limit.equiv :
  (G ⋙ forget _).sections ≃ ↥(limits.limit G) :=
let E := limits.is_limit_of_preserves (forget C) (limits.limit.is_limit G),
    F := limits.types.limit_cone_is_limit (G ⋙ forget C) in
(F.cone_point_unique_up_to_iso E).to_equiv

/-- If `C` is a concrete category for which the forgetful functor
preserves limits, then we can construct a term of `limit G` in the "usual"
way as a sequence compatible with the transition morphisms in the diagram. -/
noncomputable def limit.mk (x : Π j : J, G.obj j) (compat : ∀ ⦃i j : J⦄ (e : i ⟶ j),
  G.map e (x _) = x _) : ↥(limits.limit G) := (limit.equiv G) ⟨x,compat⟩

-- Rename this?
lemma limit.term_ext {x y : limits.limit G}
  (h : ∀ j : J, limits.limit.π G j x = limits.limit.π G j y) : x = y :=
begin
  apply_fun (limit.equiv G).symm,
  ext j,
  exact h j,
end

end concrete_category

end category_theory
