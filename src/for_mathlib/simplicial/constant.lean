import algebraic_topology.simplicial_object

namespace simplicial_object

open category_theory

variables {C : Type*} [category C]

abbreviation const : C ⥤ simplicial_object C := category_theory.functor.const _

end simplicial_object
