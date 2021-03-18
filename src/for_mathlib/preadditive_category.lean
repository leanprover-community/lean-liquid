import category_theory.abelian.additive_functor -- minimize this

namespace category_theory

namespace preadditive

variables {C : Type*} [category C] [preadditive C] {X Y Z : C}

def comp_hom : (X ⟶ Y) →+ (Y ⟶ Z) →+ (X ⟶ Z) :=
add_monoid_hom.mk' (λ f, left_comp _ f) $
  λ f₁ f₂, add_monoid_hom.ext $ λ g, (right_comp _ g).map_add f₁ f₂

end preadditive

end category_theory
