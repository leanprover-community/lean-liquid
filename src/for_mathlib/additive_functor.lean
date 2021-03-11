import category_theory.abelian.additive_functor

namespace category_theory

variables {C D E : Type*} [category C] [category D] [category E]
variables [preadditive C] [preadditive D] [preadditive E]

namespace functor

-- I like this namespace better for the following lemmas (compared to `additive.map_zero`, etc)

variables (F : C ⥤ D) (G : D ⥤ E) [additive F] [additive G] {X Y : C}

@[simp] lemma map_zero (X Y : C) :
  F.map (0 : X ⟶ Y) = 0 :=
F.map_add_hom.map_zero

@[simp] lemma map_neg (f : X ⟶ Y) :
  F.map (-f) = -F.map f :=
F.map_add_hom.map_neg f

@[simp] lemma map_add (f g : X ⟶ Y) :
  F.map (f + g) = F.map f + F.map g :=
F.map_add_hom.map_add f g

@[simp] lemma map_sub (f g : X ⟶ Y) :
  F.map (f - g) = F.map f - F.map g :=
F.map_add_hom.map_sub f g

lemma additive.comp : additive (F ⋙ G) := {}

end functor

end category_theory
