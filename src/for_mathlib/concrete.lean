import category_theory.limits.preserves.basic
import category_theory.limits.concrete_category

namespace category_theory

namespace concrete_category

universes v u
variables {C : Type u} [category.{v} C] [concrete_category.{v} C]
  {J : Type v} [small_category J] (G : J ⥤ C) [limits.has_limit G]
  [limits.preserves_limit G (forget C)]

local attribute [instance] has_coe_to_sort has_coe_to_fun

@[nolint doc_blame] --TODO add doc?
noncomputable def limit.mk (x : Π j : J, G.obj j) (compat : ∀ ⦃i j : J⦄ (e : i ⟶ j),
  G.map e (x _) = x _) : ↥(limits.limit G) :=
let E := limits.is_limit_of_preserves (forget C) (limits.limit.is_limit G),
    F := limits.types.limit_cone_is_limit (G ⋙ forget C) in
(F.cone_point_unique_up_to_iso E).hom ⟨x,compat⟩

end concrete_category

end category_theory
