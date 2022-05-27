import for_mathlib.derived.defs
import for_mathlib.homological_complex_op
import for_mathlib.commsq

noncomputable theory

open category_theory opposite
open homotopy_category

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {ι : Type*} {c : complex_shape ι}

lemma is_iso_of_square {A B C D : 𝓐} (a : A ⟶ B) (b : B ⟶ D) (a' : A ⟶ C) (c : C ⟶ D) (w : a ≫ b = a' ≫ c)
  (ha : is_iso a) (hb : is_iso b) (ha' : is_iso a') :
  is_iso c :=
begin
  have hc : c = inv a' ≫ a ≫ b, { rw [is_iso.eq_inv_comp, w], },
  rw [hc], apply_instance,
end

def homology.map' {A₁ B₁ C₁ A₂ B₂ C₂ : 𝓐}
  {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} (w₁ : f₁ ≫ g₁ = 0)
  {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} (w₂ : f₂ ≫ g₂ = 0)
  {a : A₁ ⟶ A₂} {b : B₁ ⟶ B₂} {c : C₁ ⟶ C₂}
  (sq1 : commsq f₁ a b f₂) (sq2 : commsq g₁ b c g₂) :
  homology f₁ g₁ w₁ ⟶ homology f₂ g₂ w₂ :=
homology.map w₁ w₂ ⟨a, b, sq1.w.symm⟩ ⟨b, c, sq2.w.symm⟩ rfl

lemma homology.map_eq {A₁ B₁ C₁ A₂ B₂ C₂ : 𝓐}
  {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} (w₁ : f₁ ≫ g₁ = 0)
  {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} (w₂ : f₂ ≫ g₂ = 0)
  (sq1 : arrow.mk f₁ ⟶ arrow.mk f₂) (sq2 : arrow.mk g₁ ⟶ arrow.mk g₂) (H) :
  homology.map w₁ w₂ sq1 sq2 H =
    @homology.map' _ _ _ _ _ _ _ _ _ _ _ w₁ _ _ w₂ sq1.left sq1.right sq2.right
      (commsq.of_eq sq1.w.symm) (commsq.of_eq $ by { rw H, exact sq2.w.symm }) :=
by { rw homology.map', cases sq1, cases sq2, congr, rw H, }

def commsq.op {A B C D : 𝓐} {a : A ⟶ B} {b : B ⟶ D} {a' : A ⟶ C} {c : C ⟶ D}
  (sq : commsq a a' b c) :
  commsq c.op b.op a'.op a.op :=
begin
  apply commsq.of_eq,
  simp only [← op_comp, sq.w]
end

-- SELFCONTAINED
lemma homology_map_homology_op_iso {A₁ B₁ C₁ A₂ B₂ C₂ : 𝓐}
  (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (w₁ : f₁ ≫ g₁ = 0)
  (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) (w₂ : f₂ ≫ g₂ = 0)
  (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (c : C₁ ⟶ C₂)
  (sq1 : commsq f₁ a b f₂) (sq2 : commsq g₁ b c g₂) :
  homology.map' _ _ sq2.op sq1.op ≫ (homology_op_iso f₁ g₁ w₁).hom =
  (homology_op_iso _ _ _).hom ≫ (homology.map' w₁ w₂ sq1 sq2).op :=
begin
  delta homology_op_iso, dsimp,
  sorry
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
  refine is_iso_of_square _ (homology_op_iso _ _ _).hom (homology_op_iso _ _ _).hom  _ _ aux _ _,
  swap, { apply_instance }, swap, { apply_instance },
  rw [homology.map_eq, homology.map_eq, ← homology_map_homology_op_iso],
  congr' 2,
end
