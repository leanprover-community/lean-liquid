import for_mathlib.homological_complex_op
import for_mathlib.has_homology

noncomputable theory

open category_theory opposite

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
(homology.has f₁ g₁ w₁).map (homology.has f₂ g₂ w₂) sq1 sq2

lemma homology.map_eq {A₁ B₁ C₁ A₂ B₂ C₂ : 𝓐}
  {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} (w₁ : f₁ ≫ g₁ = 0)
  {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} (w₂ : f₂ ≫ g₂ = 0)
  (sq1 : arrow.mk f₁ ⟶ arrow.mk f₂) (sq2 : arrow.mk g₁ ⟶ arrow.mk g₂) (H) :
  homology.map w₁ w₂ sq1 sq2 H =
    @homology.map' _ _ _ _ _ _ _ _ _ _ _ w₁ _ _ w₂ sq1.left sq1.right sq2.right
      (commsq.of_eq sq1.w.symm) (commsq.of_eq $ by { rw H, exact sq2.w.symm }) :=
begin
  apply (homology.has f₂ g₂ w₂).ext_ι,
  erw [has_homology.map_ι],
  apply (homology.has f₁ g₁ w₁).ext_π,
  erw [← category.assoc, homology.π'_map, category.assoc, homology.π'_ι, has_homology.π_comp_desc,
    limits.kernel.lift_ι_assoc, category.assoc],
end
