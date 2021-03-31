import category_theory.structured_arrow

namespace category_theory
universes v₁ v₂ u₁ u₂ -- morphism levels before object levels. See note [category_theory universes].
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

namespace structured_arrow
variables {S S' S'' : D} {Y Y' : C} {T : C ⥤ D}
/-- The obvious projection functor from structured arrows. -/

def proj : structured_arrow S T ⥤ C := comma.snd _ _

end structured_arrow

namespace costructured_arrow
variables {T T' T'' : D} {Y Y' : C} {S : C ⥤ D}

/-- The obviuous projection functor from costructured arrows. -/
def proj : costructured_arrow S T ⥤ C := comma.fst _ _

end costructured_arrow

end category_theory
