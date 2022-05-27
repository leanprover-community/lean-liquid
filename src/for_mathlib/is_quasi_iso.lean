import for_mathlib.derived.defs
import for_mathlib.homological_complex_op

noncomputable theory

open category_theory opposite
open homotopy_category

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {ι : Type*} {c : complex_shape ι}

-- SELFCONTAINED
lemma is_quasi_iso_of_op {X Y : (chain_complex 𝓐 ℤ)ᵒᵖ} (f : X ⟶ Y)
  (h : is_quasi_iso ((quotient _ _).map (homological_complex.op_functor.map f))) :
  is_quasi_iso ((quotient _ _).map f.unop) :=
begin
  refine ⟨λ i, _⟩,
  obtain ⟨i, rfl⟩ : ∃ j, j+1=i := ⟨i-1, sub_add_cancel _ _⟩,
  rw [← homotopy_category.homology_functor_map_factors],
  let α := (_root_.homology_functor 𝓐 _ (i + 1)).map (f.unop),
  suffices : is_iso ((homology_iso' (unop Y) (i+1+1) (i+1) i rfl rfl).inv ≫
    α ≫ (homology_iso' (unop X) (i+1+1) (i+1) i rfl rfl).hom),
  { apply_with is_iso.of_is_iso_comp_right {instances := ff},
    swap 4, { exact (homology_iso' (unop X) (i + 1 + 1) (i + 1) i rfl rfl).hom }, { apply_instance },
    apply_with is_iso.of_is_iso_comp_left {instances := ff},
    swap 2, { exact this }, { apply_instance } },
  let β := (_root_.homology_functor 𝓐ᵒᵖ _ (i+1)).map (homological_complex.op_functor.map f),
  haveI _aux : is_iso β := @is_quasi_iso.cond _ _ _ _ _ _ _ _ h (i+1),
  have hβ : is_iso ((homology_iso' (unop X).op i (i+1) (i+1+1) rfl rfl).inv ≫
    β ≫ (homology_iso' (unop Y).op i (i+1) (i+1+1) rfl rfl).hom),
  { apply_instance },
  sorry
  -- let e := homology_op_iso,
end
