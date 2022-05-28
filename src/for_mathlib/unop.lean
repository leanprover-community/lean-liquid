import category_theory.preadditive.opposite

namespace category_theory

variables {C : Type*} [category C] [preadditive C] {X Y : Cᵒᵖ}

@[simps] def unop_hom (X Y : Cᵒᵖ) : (X ⟶ Y) →+ (opposite.unop Y ⟶ opposite.unop X) :=
add_monoid_hom.mk' (λ f, f.unop) $ λ f g, unop_add _ f g

lemma unop_sum {ι : Type*} (s : finset ι) (f : ι → (X ⟶ Y)) :
  (s.sum f).unop = s.sum (λ i, (f i).unop) :=
(unop_hom X Y).map_sum _ _

lemma unop_zsmul (k : ℤ) (f : X ⟶ Y) : (k • f).unop = k • f.unop := rfl

lemma unop_neg (f : X ⟶ Y) : (-f).unop = -(f.unop) := rfl

end category_theory
