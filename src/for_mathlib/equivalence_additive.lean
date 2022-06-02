import category_theory.abelian.basic
import category_theory.preadditive.additive_functor
import category_theory.adjunction.limits

namespace category_theory

universes v u u'
variables {A : Type u} {B : Type u'} [category.{v} A] [category.{v} B]
  [abelian A] [abelian B]

instance additive_equivalence_functor (E : A ≌ B) : E.functor.additive :=
begin
  apply_with functor.additive_of_preserves_binary_biproducts { instances := ff },
  apply_instance,
  haveI : limits.preserves_colimits E.functor,
  { apply adjunction.left_adjoint_preserves_colimits,
    exact E.to_adjunction },
  apply limits.preserves_binary_biproducts_of_preserves_binary_coproducts,
  apply_instance,
end

instance additive_equivalence_inverse (E : A ≌ B) : E.inverse.additive :=
category_theory.additive_equivalence_functor E.symm

end category_theory
