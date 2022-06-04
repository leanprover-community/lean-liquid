import category_theory.preadditive.opposite

namespace category_theory

variables {C : Type*} [category C] [preadditive C] {X Y : C}

@[simps] def op_hom (X Y : C) : (X ⟶ Y) →+ (opposite.op Y ⟶ opposite.op X) :=
add_monoid_hom.mk' (λ f, f.op) $ λ f g, op_add _ f g

lemma op_sum {ι : Type*} (s : finset ι) (f : ι → (X ⟶ Y)) :
  (s.sum f).op = s.sum (λ i, (f i).op) :=
(op_hom X Y).map_sum _ _

lemma op_zsmul (k : ℤ) (f : X ⟶ Y) : (k • f).op = k • f.op := rfl

-- lemma op_neg (f : X ⟶ Y) : (-f).op = -(f.op) := rfl

end category_theory
