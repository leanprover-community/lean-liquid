import category_theory.abelian.pseudoelements

noncomputable theory

universe variables v u

namespace category_theory
open category_theory.limits

-- /-- A *cross* centered at `A` is a diagram of 4 arrows as they typically occur in a double complex:

--           U
--           |
--           | u
--           |
--      l    v    r
-- L ------> A ------> R
--           |
--           | d
--           |
--           v
--           D
--  -/
-- class cross {𝒜 : Type*} [quiver 𝒜] (A : 𝒜) :=
-- {U R D L : 𝒜}
-- (u : U ⟶ A)
-- (r : A ⟶ R)
-- (d : A ⟶ D)
-- (l : L ⟶ A)

namespace salamander

section

open subobject (of_le)

parameters {𝒜 : Type*} [category 𝒜] [abelian 𝒜]

parameters {A₁ B₁ C₁ D₁ : 𝒜}
parameters {A₂ B₂ C₂ D₂ : 𝒜}
parameters {A₃ B₃ C₃ D₃ : 𝒜}
parameters {A₄ B₄ C₄ D₄ : 𝒜}
parameters (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (h₁ : C₁ ⟶ D₁)
parameters (a₁ : A₁ ⟶ A₂) (b₁ : B₁ ⟶ B₂) (c₁ : C₁ ⟶ C₂) (d₁ : D₁ ⟶ D₂)
parameters (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) (h₂ : C₂ ⟶ D₂)
parameters (a₂ : A₂ ⟶ A₃) (b₂ : B₂ ⟶ B₃) (c₂ : C₂ ⟶ C₃) (d₂ : D₂ ⟶ D₃)
parameters (f₃ : A₃ ⟶ B₃) (g₃ : B₃ ⟶ C₃) (h₃ : C₃ ⟶ D₃)
parameters (a₃ : A₃ ⟶ A₄) (b₃ : B₃ ⟶ B₄) (c₃ : C₃ ⟶ C₄) (d₃ : D₃ ⟶ D₄)
parameters (f₄ : A₄ ⟶ B₄) (g₄ : B₄ ⟶ C₄) (h₄ : C₄ ⟶ D₄)

-- A║ A═ ▝A A▖

def image_le_kernel_inf_kernel (hf : f₂ ≫ g₂ = 0) (hb : b₁ ≫ b₂ = 0) (h : a₁ ≫ f₂ = f₁ ≫ b₁) :
  image_subobject (f₁ ≫ b₁) ≤ (kernel_subobject b₂ ⊓ kernel_subobject g₂) :=
begin
  refine le_inf _ _; apply le_kernel_subobject;
  rw [← cancel_epi (factor_thru_image_subobject $ f₁ ≫ b₁), ← category.assoc,
    image_subobject_arrow_comp],
  { rw [category.assoc, hb, comp_zero, comp_zero] },
  { rw [← h, category.assoc, hf, comp_zero, comp_zero] }
end

lemma image_sup_image_le_kernel (hf : f₂ ≫ g₂ = 0) (hb : b₁ ≫ b₂ = 0)
  (h : b₂ ≫ g₃ = g₂ ≫ c₂) :
  (image_subobject f₂ ⊔ image_subobject b₁) ≤ kernel_subobject (g₂ ≫ c₂) :=
begin
  refine sup_le _ _; apply le_kernel_subobject,
  { rw [← cancel_epi (factor_thru_image_subobject f₂), ← category.assoc, image_subobject_arrow_comp,
      ← category.assoc, hf, zero_comp, comp_zero], },
  { rw [← cancel_epi (factor_thru_image_subobject b₁), ← category.assoc, image_subobject_arrow_comp,
      ← h, ← category.assoc, hb, zero_comp, comp_zero], },
end

def receptor (hf : f₂ ≫ g₂ = 0) (hb : b₁ ≫ b₂ = 0) (h : a₁ ≫ f₂ = f₁ ≫ b₁) :=
cokernel (of_le _ _ (image_le_kernel_inf_kernel hf hb h))

def donor (hf : f₂ ≫ g₂ = 0) (hb : b₁ ≫ b₂ = 0) (h : b₂ ≫ g₃ = g₂ ≫ c₂) :=
cokernel (of_le _ _ (image_sup_image_le_kernel hf hb h))

/-- Intramural morphism -/
def receptor_to_horizontal (hf : f₂ ≫ g₂ = 0) (hb : b₁ ≫ b₂ = 0) (h : a₁ ≫ f₂ = f₁ ≫ b₁) :
  receptor hf hb h ⟶ homology _ _ hf :=
begin
  refine cokernel.map _ _ (of_le _ _ $ _) (of_le _ _ $ inf_le_right) _,
  { simp only [← h], apply image_subobject_comp_le, },
  { simp only [image_to_kernel, subobject.of_le_comp_of_le], }
end

/-- Intramural morphism -/
def receptor_to_vertical (hf : f₂ ≫ g₂ = 0) (hb : b₁ ≫ b₂ = 0) (h : a₁ ≫ f₂ = f₁ ≫ b₁) :
  receptor hf hb h ⟶ homology _ _ hb :=
begin
  refine cokernel.map _ _ (of_le _ _ $ _) (of_le _ _ $ inf_le_left) _,
  { apply image_subobject_comp_le, },
  { simp only [image_to_kernel, subobject.of_le_comp_of_le], }
end

/-- Intramural morphism -/
def horizontal_to_donor (hf : f₂ ≫ g₂ = 0) (hb : b₁ ≫ b₂ = 0) (h : b₂ ≫ g₃ = g₂ ≫ c₂) :
  homology _ _ hf ⟶ donor hf hb h :=
begin
  refine cokernel.map _ _ (of_le _ _ $ le_sup_left) (of_le _ _ $ _) _,
  { apply le_kernel_subobject, simp only [zero_comp, kernel_subobject_arrow_comp_assoc], },
  { simp only [image_to_kernel, subobject.of_le_comp_of_le], }
end

/-- Intramural morphism -/
def vertical_to_donor (hf : f₂ ≫ g₂ = 0) (hb : b₁ ≫ b₂ = 0) (h : b₂ ≫ g₃ = g₂ ≫ c₂) :
  homology _ _ hb ⟶ donor hf hb h :=
begin
  refine cokernel.map _ _ (of_le _ _ $ le_sup_right) (of_le _ _ $ _) _,
  { apply le_kernel_subobject, simp only [zero_comp, kernel_subobject_arrow_comp_assoc, ← h], },
  { simp only [image_to_kernel, subobject.of_le_comp_of_le], }
end

lemma receptor_to_horizontal_comp_horizontal_to_donor
  (hf : f₂ ≫ g₂ = 0) (hb : b₁ ≫ b₂ = 0) (hr : a₁ ≫ f₂ = f₁ ≫ b₁) (hd : b₂ ≫ g₃ = g₂ ≫ c₂) :
  receptor_to_horizontal hf hb hr ≫ horizontal_to_donor hf hb hd =
  receptor_to_vertical hf hb hr ≫ vertical_to_donor hf hb hd :=
begin
  dsimp only [receptor_to_horizontal, horizontal_to_donor, receptor_to_vertical, vertical_to_donor],
  apply coequalizer.hom_ext,
  show cokernel.π _ ≫ _ = cokernel.π _ ≫ _,
  simp only [cokernel.π_desc, cokernel.π_desc_assoc,
    subobject.of_le_comp_of_le_assoc, category.assoc],
end

end

section

parameters {𝒜 : Type*} [category 𝒜] [abelian 𝒜]

parameters {A₁ B₁ C₁ D₁ : 𝒜}
parameters {A₂ B₂ C₂ D₂ : 𝒜}
parameters {A₃ B₃ C₃ D₃ : 𝒜}
parameters {A₄ B₄ C₄ D₄ : 𝒜}
parameters (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (h₁ : C₁ ⟶ D₁)
parameters (a₁ : A₁ ⟶ A₂) (b₁ : B₁ ⟶ B₂) (c₁ : C₁ ⟶ C₂) (d₁ : D₁ ⟶ D₂)
parameters (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) (h₂ : C₂ ⟶ D₂)
parameters (a₂ : A₂ ⟶ A₃) (b₂ : B₂ ⟶ B₃) (c₂ : C₂ ⟶ C₃) (d₂ : D₂ ⟶ D₃)
parameters (f₃ : A₃ ⟶ B₃) (g₃ : B₃ ⟶ C₃) (h₃ : C₃ ⟶ D₃)
parameters (a₃ : A₃ ⟶ A₄) (b₃ : B₃ ⟶ B₄) (c₃ : C₃ ⟶ C₄) (d₃ : D₃ ⟶ D₄)
parameters (f₄ : A₄ ⟶ B₄) (g₄ : B₄ ⟶ C₄) (h₄ : C₄ ⟶ D₄)

/-- Extramural morphism -/
def v_ex (hf₂ : f₂ ≫ g₂ = 0) (hb₁ : b₁ ≫ b₂ = 0) (sq₁ : b₂ ≫ g₃ = g₂ ≫ c₂)
  (hf₃ : f₃ ≫ g₃ = 0) (hb₂ : b₂ ≫ b₃ = 0) (sq₂ : a₂ ≫ f₃ = f₂ ≫ b₂) :
  donor b₁ f₂ g₂ b₂ c₂ g₃ hf₂ hb₁ sq₁ ⟶ receptor f₂ a₂ b₂ f₃ g₃ b₃ hf₃ hb₂ sq₂ :=
begin
  refine cokernel.map _ _ _ _ _; sorry
end

/-- Extramural morphism -/
def h_ex (hf₂ : f₂ ≫ g₂ = 0) (hb₁ : b₁ ≫ b₂ = 0) (sq₁ : b₂ ≫ g₃ = g₂ ≫ c₂)
  (hg₂ : g₂ ≫ h₂ = 0) (hc₁ : c₁ ≫ c₂ = 0) (sq₂ : b₁ ≫ g₂ = g₁ ≫ c₁) :
  donor b₁ f₂ g₂ b₂ c₂ g₃ hf₂ hb₁ sq₁ ⟶ receptor g₁ b₁ c₁ g₂ h₂ c₂ hg₂ hc₁ sq₂ :=
begin
  refine cokernel.map _ _ _ _ _; sorry
end

end

end salamander

end category_theory
