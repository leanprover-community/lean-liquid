import topology.discrete_quotient
import topology.category.Profinite
import for_mathlib.SemiNormedGroup

open category_theory
open category_theory.limits

universes u

namespace locally_constant
variables {M : Type*} {X : Profinite.{u}}

/-- Construct a discrete quotient from a locally constant function. -/
def to_discrete_quotient (f : locally_constant X M) : discrete_quotient X :=
{ rel := λ a b, f a = f b,
  equiv := ⟨by tauto, by tauto, λ a b c h1 h2, by rw [h1, h2]⟩,
  clopen := λ x, ⟨is_locally_constant _ _,
    ⟨by {erw ← set.preimage_compl, apply is_locally_constant _ _ }⟩⟩ }

end locally_constant

/-
lemma Profinite.locally_constant_factors
  {J : Type u} [small_category.{u} J] [is_filtered Jᵒᵖ]
  (F : J ⥤ Profinite.{u}) (S : Type*) (f : locally_constant ↥(limit F) S) :
  ∃ (j : J) (g : locally_constant (F.obj j) S),
  g ∘ (limit.π F j) = f := by admit
-/
