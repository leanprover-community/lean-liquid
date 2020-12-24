import NormedGroup

/-- A `normed_with_aut r V` structure on a normed abelian group `V`
consists of an automorphism `T` satisfying `∥T v∥ = r * ∥v∥`.

In other words, it is a normed `ℤ[T^{±1}]`-module satisfying `∥T v∥ = r * ∥v∥`.

Definition 8.13 of [Analytic] -/
class normed_with_aut (r : out_param ℝ) (V : NormedGroup) :=
(T : V ≅ V)
(norm_T : ∀ v : V, ∥(T.hom : V → V) v∥ = r * ∥v∥)
