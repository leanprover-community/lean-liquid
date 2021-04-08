import category_theory.preadditive.additive_functor

namespace category_theory

variables {C D E : Type*} [category C] [category D] [category E]
variables [preadditive C] [preadditive D] [preadditive E]

namespace functor

-- I like this namespace better for the following lemmas (compared to `additive.map_zero`, etc)

variables (F : C ⥤ D) (G : D ⥤ E) [additive F] [additive G] {X Y : C}

lemma additive.comp : additive (F ⋙ G) := {}

end functor

end category_theory
