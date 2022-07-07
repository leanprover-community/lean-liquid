import category_theory.limits.shapes.products

open category_theory
namespace category_theory.limits

universes v u
variables  (C : Type u) [category.{v} C]
 (α : Type v) [has_products_of_shape α C]

noncomputable theory
def pow_functor : C ⥤ C :=
{ obj := λ X, (∏ λ i : α, X),
  map := λ X Y f, pi.map $ λ i, f }

end category_theory.limits
