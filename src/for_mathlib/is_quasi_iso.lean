import for_mathlib.derived.defs
import for_mathlib.homology_map
import for_mathlib.has_homology

noncomputable theory

open category_theory opposite
open homotopy_category

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {ι : Type*} {c : complex_shape ι}

def commsq.op {A B C D : 𝓐} {a : A ⟶ B} {b : B ⟶ D} {a' : A ⟶ C} {c : C ⟶ D}
  (sq : commsq a a' b c) :
  commsq c.op b.op a'.op a.op :=
begin
  apply commsq.of_eq,
  simp only [← op_comp, sq.w]
end

lemma homology_map_homology_op_iso {A₁ B₁ C₁ A₂ B₂ C₂ : 𝓐}
  (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (w₁ : f₁ ≫ g₁ = 0)
  (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) (w₂ : f₂ ≫ g₂ = 0)
  (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (c : C₁ ⟶ C₂)
  (sq1 : commsq f₁ a b f₂) (sq2 : commsq g₁ b c g₂) :
  homology.map' _ _ sq2.op sq1.op ≫ (has_homology.homology_op_iso f₁ g₁ w₁).hom =
  (has_homology.homology_op_iso _ _ _).hom ≫ (homology.map' w₁ w₂ sq1 sq2).op :=
begin
  suffices : (homology.map' w₁ w₂ sq1 sq2).op =
    (homology.has _ _ _).op.map (homology.has _ _ _).op sq2.op sq1.op,
  { erw [this, has_homology.map_comp_map, has_homology.map_comp_map],
    apply (homology.has _ _ _).ext_π,
    apply (homology.has _ _ _).op.ext_ι,
    simp only [has_homology.π_map, has_homology.lift_comp_ι, iso.refl_hom],
    erw [has_homology.lift_comp_ι],
    congr' 2, rw [category.id_comp, category.comp_id], },
  apply (homology.has _ _ _).op.ext_π,
  apply (homology.has _ _ _).op.ext_ι,
  simp only [has_homology.π_map, has_homology.lift_comp_ι],
  dsimp only [has_homology.op, kernel_op_op_hom, cokernel_op_op_inv],
  simp only [← op_comp, homology.map', category.assoc, has_homology.π_map_assoc,
    has_homology.lift_comp_ι_assoc, limits.kernel.lift_ι_assoc, limits.cokernel.π_desc],
  simp only [op_comp, category.assoc],
  refl,
end

lemma is_quasi_iso_of_op {X Y : (chain_complex 𝓐 ℤ)ᵒᵖ} (f : X ⟶ Y)
  (h : is_quasi_iso ((quotient _ _).map (homological_complex.op_functor.map f))) :
  is_quasi_iso ((quotient _ _).map f.unop) :=
begin
  refine ⟨λ i, _⟩,
  obtain ⟨i, rfl⟩ : ∃ j, j+1=i := ⟨i-1, sub_add_cancel _ _⟩,
  rw [← homotopy_category.homology_functor_map_factors, homology_iso_map (i+1+1) (i+1) i],
  swap, {dsimp, refl}, swap, {dsimp, refl},
  apply_with is_iso.comp_is_iso {instances:=ff}, { apply_instance },
  apply_with is_iso.comp_is_iso {instances:=ff}, swap, { apply_instance },
  have aux := @is_quasi_iso.cond _ _ _ _ _ _ _ _ h (i+1),
  rw [← homotopy_category.homology_functor_map_factors, homology_iso_map i (i+1) (i+1+1)] at aux,
  swap, {dsimp, refl}, swap, {dsimp, refl},
  replace aux := @is_iso.of_is_iso_comp_left _ _ _ _ _ _ _ _ aux,
  replace aux := @is_iso.of_is_iso_comp_right _ _ _ _ _ _ _ _ aux,
  rw [← is_iso_op_iff],
  refine is_iso_of_square _ (has_homology.homology_op_iso _ _ _).hom (has_homology.homology_op_iso _ _ _).hom  _ _ aux _ _,
  swap, { apply_instance }, swap, { apply_instance },
  rw [homology.map_eq, homology.map_eq, ← homology_map_homology_op_iso],
  congr' 2,
end
