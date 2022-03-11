import for_mathlib.derived.K_projective
import for_mathlib.complex_extend

.

universes v u

open category_theory

variables {C : Type u} [category.{v} C] [abelian C] [enough_projectives C]
variables (A : Cᵒᵖ) (B : C)

lemma AddCommGroup.is_zero_of_eq (A : AddCommGroup) (h : ∀ x y : A, x = y) :
  is_zero A :=
{ eq_zero_of_src := λ B f, by { ext, cases h x 0, exact f.map_zero },
  eq_zero_of_tgt := λ B f, by { ext, exact h _ _ } }

lemma Ext_is_zero_of_neg (i : ℤ) (hi : i < 0) :
  is_zero (((Ext' i).obj A).obj B) :=
begin
  refine AddCommGroup.is_zero_of_eq _ _,
  dsimp [Ext', bounded_homotopy_category.Ext],
  intros f g,
  sorry
end
