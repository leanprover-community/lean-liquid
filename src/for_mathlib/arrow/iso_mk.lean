import category_theory.arrow

namespace category_theory
namespace arrow

universes v u

variables {C : Type u} [category.{v} C]

def iso_mk {f g : arrow C} (l : f.left ≅ g.left) (r : f.right ≅ g.right)
  (h : l.hom ≫ g.hom = f.hom ≫ r.hom) :
  f ≅ g :=
comma.iso_mk l r h

end arrow
end category_theory
