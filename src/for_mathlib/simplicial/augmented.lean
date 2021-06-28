import order.omega_complete_partial_order -- for preorder_hom.const
import algebraic_topology.simplicial_object

open opposite category_theory category_theory.limits
open simplex_category

universes v u

namespace category_theory

namespace simplex_category

@[simp] lemma hom_zero_zero (f : mk 0 ⟶ mk 0) : f = 𝟙 _ :=
by { ext : 2, dsimp, exact subsingleton.elim _ _ }

end simplex_category

end category_theory
