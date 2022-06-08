import for_mathlib.derived.ext_coproducts

.

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

namespace bounded_homotopy_category

instance uniformly_bounded_single {α : Type v} (i : ℤ) (X : α → A) :
  uniformly_bounded (λ a : α, (single A i).obj (X a)) :=
begin
  refine ⟨⟨i+1, λ a k hk, _⟩⟩,
  dsimp only [single, homotopy_category.single, functor.comp_obj, function.comp_app,
    homotopy_category.quotient_obj_as, homological_complex.single],
  rw if_neg,
  { exact is_zero_zero _ },
  { rintro rfl, linarith only [hk] }
end

instance has_coproduct_of_shape_single {α : Type v} (i : ℤ)
  [has_coproducts_of_shape α A]
  (X : α → A) : has_coproduct (λ a, (single A i).obj (X a)) :=
sorry

def single_sigma_iso {α : Type v} (i : ℤ) (X : α → A)
  [has_coproducts_of_shape α A] :
  (single A i).obj (∐ X) ≅ ∐ λ (a : α), (single A i).obj (X a) := sorry

noncomputable
instance preserves_coproducts_single {α : Type v}
  [has_coproducts_of_shape α A]
  (i : ℤ) :
  preserves_colimits_of_shape (discrete α) (single A i) :=
begin
  refine preserves_coproducts_aux _ _ _,
  { sorry },
  { sorry }
  -- { intro X,
  --   refine ⟨_, sigma.desc (λ a, (single A i).map (sigma.ι _ _)), _, _⟩,
  --   { sorry },
  --   { sorry },
  --   { sorry }, },
  -- { intros X a, sorry },
end

variables [enough_projectives A]

instance preserves_coproducts_Ext' {α : Type v} (i : ℤ) (Y : A) :
  preserves_colimits_of_shape (discrete α)
  ((Ext' i).flip.obj Y).right_op := sorry

end bounded_homotopy_category
