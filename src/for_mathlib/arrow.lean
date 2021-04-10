import category_theory.arrow

namespace category_theory

theorem arrow.mk_inj {T} [category T] (A B : T) (f g : A ⟶ B) : arrow.mk f = arrow.mk g → f = g :=
by rintro ⟨⟩; refl

end category_theory
