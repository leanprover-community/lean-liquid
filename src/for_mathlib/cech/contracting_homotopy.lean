import .split
import for_mathlib.simplicial.complex

open_locale big_operators

noncomputable theory

namespace category_theory

namespace cech

universes v u

variables {P : Type v} {C : Type u} [small_category P] [category.{v} C] [preadditive C]
variables {X B : P} (f : X ⟶ B) [∀ (n : ℕ), limits.has_wide_pullback B (λ (i : ufin (n+1)), X) (λ i, f)]
variables (M : Pᵒᵖ ⥤ C)
variables (g : B ⟶ X) (splitting : g ≫ f = 𝟙 B)

abbreviation conerve : cosimplicial_object C := (cech_obj f).right_op ⋙ M

abbreviation conerve_complex : cochain_complex ℕ C := cosimplicial_object.cocomplex.obj $ conerve f M

abbreviation contracting_homotopy (n : ℕ) :
  (conerve_complex f M).X (n+1) ⟶ (conerve_complex f M).X n :=
M.map $ (cech_splitting f g splitting n).op

theorem is_contracting_homotopy (n : ℕ) :
  (conerve_complex f M).d (n+1) (n+2) ≫ contracting_homotopy f M g splitting (n+1) -
  contracting_homotopy f M g splitting n ≫ (conerve_complex f M).d n (n+1) = 𝟙 _ :=
begin
  delta conerve_complex,
  dsimp only [cosimplicial_object.cocomplex, cosimplicial_object.to_cocomplex, cochain_complex.mk'],
  split_ifs,
  swap, finish,
  swap, finish,
  swap, finish,
  dsimp only [cosimplicial_object.coboundary],
  simp only [preadditive.sum_comp, preadditive.comp_sum],
  sorry
end

end cech

end category_theory
