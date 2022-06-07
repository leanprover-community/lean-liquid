import algebra.homology.homology
import category_theory.abelian.homology

import for_mathlib.commsq
import for_mathlib.exact_lift_desc

noncomputable theory

universes v u

open category_theory category_theory.limits

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]
variables {A B C : 𝓐} {f : A ⟶ B} {g : B ⟶ C} {H : 𝓐}

structure has_homology (f : A ⟶ B) (g : B ⟶ C) (H : 𝓐) :=
(w : f ≫ g = 0)
(π : kernel g ⟶ H)
(ι : H ⟶ cokernel f)
(π_ι : π ≫ ι = kernel.ι _ ≫ cokernel.π _)
(ex_π : exact (kernel.lift g f w) π)
(ι_ex : exact ι (cokernel.desc f g w))
[epi_π : epi π]
[mono_ι : mono ι]

def homology.has (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  has_homology f g (homology f g w) :=
{ w := w,
  π := homology.π' f g w,
  ι := homology.ι f g w,
  π_ι := homology.π'_ι _ _ _,
  ex_π := begin
    delta homology.π',
    rw exact_comp_iso,
    exact abelian.exact_cokernel _
  end,
  ι_ex := begin
    delta homology.ι,
    rw exact_iso_comp,
    exact exact_kernel_ι
  end,
  epi_π := by { delta homology.π', apply epi_comp },
  mono_ι := by { delta homology.ι, apply mono_comp } }

namespace has_homology

attribute [instance] epi_π mono_ι
attribute [reassoc] π_ι

section misc

@[simp, reassoc] lemma ι_desc (hH : has_homology f g H) : hH.ι ≫ cokernel.desc f g hH.w = 0 := hH.ι_ex.w

@[simp, reassoc] lemma lift_π (hH : has_homology f g H) : kernel.lift g f hH.w ≫ hH.π = 0 := hH.ex_π.w

end misc

section ext

lemma ext_π (hH : has_homology f g H) {X : 𝓐} (φ ψ : H ⟶ X) (h : hH.π ≫ φ = hH.π ≫ ψ) : φ = ψ :=
by rwa cancel_epi at h

lemma ext_ι (hH : has_homology f g H) {X : 𝓐} (φ ψ : X ⟶ H) (h : φ ≫ hH.ι = ψ ≫ hH.ι) : φ = ψ :=
by rwa cancel_mono at h

end ext

section lift

variables (hH : has_homology f g H)
variables {X : 𝓐} (φ : X ⟶ cokernel f) (hφ : φ ≫ cokernel.desc f g hH.w = 0)

def lift : X ⟶ H := hH.ι_ex.mono_lift φ hφ

@[simp, reassoc] lemma lift_comp_ι : hH.lift φ hφ ≫ hH.ι = φ := hH.ι_ex.mono_lift_comp φ hφ

lemma lift_unique (e : X ⟶ H) (he : e ≫ hH.ι = φ) : e = hH.lift φ hφ :=
hH.ι_ex.mono_lift_unique _ _ e he

@[simp] lemma lift_ι : hH.lift hH.ι hH.ι_desc = 𝟙 H :=
(hH.lift_unique _ _ _ $ category.id_comp _).symm

lemma π_eq_lift : hH.π =
  hH.lift (kernel.ι _ ≫ cokernel.π _) (by simp only [category.assoc, cokernel.π_desc, kernel.condition]) :=
lift_unique _ _ _ _ hH.π_ι

@[reassoc] lemma comp_lift {X Y : 𝓐} (φ : X ⟶ Y) (ψ : Y ⟶ cokernel f) (hψ : ψ ≫ cokernel.desc f g hH.w = 0) :
  φ ≫ hH.lift ψ hψ = hH.lift (φ ≫ ψ) (by rw [category.assoc, hψ, comp_zero]) :=
by { apply lift_unique, rw [category.assoc, lift_comp_ι] }

end lift

section desc

variables (hH : has_homology f g H)
variables {X : 𝓐} (φ : kernel g ⟶ X) (hφ : kernel.lift g f hH.w ≫ φ = 0)

def desc : H ⟶ X := hH.ex_π.epi_desc φ hφ

@[simp, reassoc] lemma π_comp_desc : hH.π ≫ hH.desc φ hφ = φ := hH.ex_π.comp_epi_desc φ hφ

lemma desc_unique (e : H ⟶ X) (he : hH.π ≫ e = φ) : e = hH.desc φ hφ :=
hH.ex_π.epi_desc_unique _ _ e he

@[simp] lemma desc_π : hH.desc hH.π hH.lift_π = 𝟙 H :=
(hH.desc_unique _ _ _ $ category.comp_id _).symm

lemma ι_eq_desc : hH.ι =
  hH.desc (kernel.ι _ ≫ cokernel.π _) (by simp only [kernel.lift_ι_assoc, cokernel.condition]) :=
desc_unique _ _ _ _ hH.π_ι

@[reassoc] lemma desc_comp {X Y : 𝓐} (φ : kernel g ⟶ X) (ψ : X ⟶ Y) (hφ : kernel.lift g f hH.w ≫ φ = 0) :
  hH.desc φ hφ ≫ ψ = hH.desc (φ ≫ ψ) (by rw [reassoc_of hφ, zero_comp]) :=
by { apply desc_unique, rw [π_comp_desc_assoc] }

end desc

section map

variables {A₁ B₁ C₁ H₁ A₂ B₂ C₂ H₂ A₃ B₃ C₃ H₃ : 𝓐}
variables {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} (h₁ : has_homology f₁ g₁ H₁)
variables {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} (h₂ : has_homology f₂ g₂ H₂)
variables {f₃ : A₃ ⟶ B₃} {g₃ : B₃ ⟶ C₃} (h₃ : has_homology f₃ g₃ H₃)
variables {α : A₁ ⟶ A₂} {β : B₁ ⟶ B₂} {γ : C₁ ⟶ C₂}
variables {α' : A₂ ⟶ A₃} {β' : B₂ ⟶ B₃} {γ' : C₂ ⟶ C₃}
variables (sq1 : commsq f₁ α β f₂) (sq2 : commsq g₁ β γ g₂)
variables (sq1' : commsq f₂ α' β' f₃) (sq2' : commsq g₂ β' γ' g₃)

include h₁ h₂ sq1 sq2

def map : H₁ ⟶ H₂ :=
h₁.desc (h₂.lift (kernel.ι _ ≫ β ≫ cokernel.π _) $
  by simp only [category.assoc, cokernel.π_desc, ← sq2.w, kernel.condition_assoc, zero_comp]) $
begin
  apply h₂.ext_ι,
  simp only [category.assoc, zero_comp, h₂.lift_comp_ι, kernel.lift_ι_assoc, sq1.w_assoc,
    cokernel.condition, comp_zero],
end

omit h₁ h₂ sq1 sq2

@[simp, reassoc] lemma π_map :
  h₁.π ≫ h₁.map h₂ sq1 sq2 = (h₂.lift (kernel.ι _ ≫ β ≫ cokernel.π _) $
  by simp only [category.assoc, cokernel.π_desc, ← sq2.w, kernel.condition_assoc, zero_comp]) :=
h₁.π_comp_desc _ _

@[simp, reassoc] lemma map_ι :
  h₁.map h₂ sq1 sq2 ≫ h₂.ι = (h₁.desc (kernel.ι _ ≫ β ≫ cokernel.π _) $
  by simp only [kernel.lift_ι_assoc, sq1.w_assoc, cokernel.condition, comp_zero]) :=
by { apply h₁.desc_unique, rw [h₁.π_map_assoc, h₂.lift_comp_ι] }

@[simp, reassoc] lemma lift_map
  {X : 𝓐} (φ : X ⟶ cokernel f₁) (hφ : φ ≫ cokernel.desc f₁ g₁ h₁.w = 0) :
  h₁.lift φ hφ ≫ h₁.map h₂ sq1 sq2 = h₂.lift (φ ≫ cokernel.map f₁ f₂ α β sq1.w)
    (by { rw [category.assoc, cokernel.map_desc, reassoc_of hφ, zero_comp], exact sq2.w }) :=
begin
  apply lift_unique, rw [category.assoc, map_ι],
  conv_rhs { rw [← lift_comp_ι h₁ φ hφ, category.assoc] },
  congr' 1,
  apply h₁.ext_π,
  rw [π_comp_desc, π_ι_assoc, cokernel.π_desc],
end

-- move this
attribute [reassoc] limits.kernel.lift_map

@[simp, reassoc] lemma map_desc
  {X : 𝓐} (φ : kernel g₂ ⟶ X) (hφ : kernel.lift g₂ f₂ h₂.w ≫ φ = 0) :
  h₁.map h₂ sq1 sq2 ≫ h₂.desc φ hφ = h₁.desc (kernel.map g₁ g₂ β γ sq2.w ≫ φ)
    (by { rw [category_theory.limits.kernel.lift_map_assoc, hφ, comp_zero], exact sq1.w }) :=
begin
  apply desc_unique, rw [π_map_assoc],
  conv_rhs { rw [← π_comp_desc h₂ φ hφ, ← category.assoc] },
  congr' 1,
  apply h₂.ext_ι,
  rw [lift_comp_ι, category.assoc, π_ι, kernel.lift_ι_assoc, category.assoc],
end

def _root_.commsq.vcomp : commsq f₁ (α ≫ α') (β ≫ β') f₃ :=
commsq.of_eq $
calc f₁ ≫ β ≫ β' = α ≫ f₂ ≫ β'   : sq1.w_assoc β'
              ... = α ≫ α' ≫ f₃   : congr_arg _ $ sq1'.w
              ... = (α ≫ α') ≫ f₃ : (category.assoc _ _ _).symm

def _root_.commsq.vrefl (f : A ⟶ B) : commsq f (iso.refl _).hom (iso.refl _).hom f :=
commsq.of_eq $ by rw [iso.refl_hom, iso.refl_hom, category.id_comp, category.comp_id]

def _root_.commsq.vinv {α : A₁ ≅ A₂} {β : B₁ ≅ B₂} (sq1 : commsq f₁ α.hom β.hom f₂) :
  commsq f₂ α.inv β.inv f₁ :=
commsq.of_eq $ by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, sq1.w]

lemma map_comp_map :
  h₁.map h₂ sq1 sq2 ≫ h₂.map h₃ sq1' sq2' = h₁.map h₃ (sq1.vcomp sq1') (sq2.vcomp sq2') :=
begin
  apply h₁.ext_π, apply h₃.ext_ι,
  simp only [category.assoc, map_ι, map_desc, π_comp_desc, kernel.lift_ι_assoc],
end

lemma map_id (h : has_homology f g H) {α : A ⟶ A} {β : B ⟶ B} {γ : C ⟶ C}
  (sq1 : commsq f α β f) (sq2 : commsq g β γ g) (hβ : β = 𝟙 _) :
  h.map h sq1 sq2 = 𝟙 H :=
begin
  apply h.ext_π, apply h.ext_ι,
  rw [π_map, lift_comp_ι, category.comp_id, π_ι, hβ, category.id_comp],
end

@[simps] def map_iso {α : A₁ ≅ A₂} {β : B₁ ≅ B₂} {γ : C₁ ≅ C₂}
  (sq1 : commsq f₁ α.hom β.hom f₂) (sq2 : commsq g₁ β.hom γ.hom g₂) :
  H₁ ≅ H₂ :=
{ hom := h₁.map h₂ sq1 sq2,
  inv := h₂.map h₁ sq1.vinv sq2.vinv,
  hom_inv_id' := by { rw [map_comp_map, map_id], exact β.hom_inv_id },
  inv_hom_id' := by { rw [map_comp_map, map_id], exact β.inv_hom_id } }

abbreviation iso (h₁ : has_homology f g H₁) (h₂ : has_homology f g H₂) :
  H₁ ≅ H₂ :=
map_iso h₁ h₂ (_root_.commsq.vrefl f) (_root_.commsq.vrefl g)

end map

section op

open opposite

def op (h : has_homology f g H) : has_homology g.op f.op (op H) :=
{ w := by rw [← op_comp, h.w, op_zero],
  π := (kernel_op_op f).hom ≫ h.ι.op,
  ι := h.π.op ≫ (cokernel_op_op g).inv,
  π_ι := by {
    simp only [kernel_op_op_hom, cokernel_op_op_inv, ← op_comp, category.assoc, h.π_ι_assoc,
      kernel.lift_ι_assoc, cokernel.π_desc], refl, },
  ex_π := begin
    rw [← exact_comp_hom_inv_comp_iff (kernel_op_op f), iso.inv_hom_id_assoc, kernel_op_op_hom],
    convert h.ι_ex.op using 1,
    apply quiver.hom.unop_inj,
    apply category_theory.limits.coequalizer.hom_ext,
    erw [unop_comp, coequalizer.π_desc_assoc, coequalizer.π_desc],
    rw [← unop_comp, kernel.lift_ι, g.unop_op],
  end,
  ι_ex := begin
    rw [← exact_comp_hom_inv_comp_iff (cokernel_op_op g), category.assoc, iso.inv_hom_id,
      category.comp_id, cokernel_op_op_inv],
    convert h.ex_π.op using 1,
    apply quiver.hom.unop_inj,
    apply category_theory.limits.equalizer.hom_ext,
    erw [unop_comp, equalizer.lift_ι, category.assoc, equalizer.lift_ι],
    rw [← unop_comp, cokernel.π_desc, f.unop_op],
  end,
  epi_π := epi_comp _ _,
  mono_ι := mono_comp _ _ }

-- @[simps]
def homology_unop_iso {A B C : 𝓐ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  homology f g w ≅ opposite.op (homology g.unop f.unop (by { rw [← unop_comp, w, unop_zero] })) :=
(homology.has f g w).iso (homology.has g.unop f.unop _).op

def homology_op_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  homology g.op f.op (by rw [← op_comp, w, op_zero]) ≅ opposite.op (homology f g w) :=
homology_unop_iso _ _ _

end op

end has_homology
