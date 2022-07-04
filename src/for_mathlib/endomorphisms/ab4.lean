import for_mathlib.endomorphisms.basic
import for_mathlib.ab4

noncomputable theory

universes v u

open category_theory category_theory.limits

namespace category_theory

namespace endomorphisms

variables (𝓐 : Type u) [category.{v} 𝓐] [has_coproducts 𝓐] [AB4 𝓐]

instance : AB4 (endomorphisms 𝓐) :=
sorry

end endomorphisms

end category_theory
