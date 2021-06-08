import analysis.normed_space.normed_group_hom

noncomputable theory

open_locale nnreal

variables {V V₁ V₂ V₃ V₄ W W₁ W₂ W₃ : Type*}
variables [semi_normed_group V] [semi_normed_group V₁] [semi_normed_group V₂]
[semi_normed_group V₃] [semi_normed_group V₄]
variables [semi_normed_group W] [semi_normed_group W₁] [semi_normed_group W₂] [semi_normed_group W₃]
variables (f g : normed_group_hom V W)
variables {f₁ g₁ : normed_group_hom V₁ W₁}
variables {f₂ g₂ : normed_group_hom V₂ W₂}
variables {f₃ g₃ : normed_group_hom V₃ W₃}

namespace normed_group_hom

-- move this
lemma comp_assoc (h : normed_group_hom V₃ V₄) (g : normed_group_hom V₂ V₃)
  (f : normed_group_hom V₁ V₂) :
  (h.comp g).comp f = h.comp (g.comp f) :=
by { ext, refl }

def equalizer := (f - g).ker

namespace equalizer

def ι : normed_group_hom (f.equalizer g) V := incl _

lemma condition : f.comp (ι f g) = g.comp (ι f g) :=
by { ext, rw [comp_apply, comp_apply, ← sub_eq_zero, ← normed_group_hom.sub_apply], exact x.2 }

variables {f g}

@[simps]
def lift (φ : normed_group_hom V₁ V) (h : f.comp φ = g.comp φ) :
  normed_group_hom V₁ (f.equalizer g) :=
{ to_fun := λ v, ⟨φ v, show (f - g) (φ v) = 0,
    by rw [normed_group_hom.sub_apply, sub_eq_zero, ← comp_apply, h, comp_apply]⟩,
  map_add' := λ v₁ v₂, by { ext, simp only [map_add, add_subgroup.coe_add, subtype.coe_mk] },
  bound' := by { obtain ⟨C, C_pos, hC⟩ := φ.bound, exact ⟨C, hC⟩ } }

@[simp] lemma lift_ι (φ : normed_group_hom V₁ V) (h : f.comp φ = g.comp φ) :
  (ι _ _).comp (lift φ h) = φ :=
by { ext, refl }

def map (φ : normed_group_hom V₁ V₂) (ψ : normed_group_hom W₁ W₂)
  (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) :
  normed_group_hom (f₁.equalizer g₁) (f₂.equalizer g₂) :=
lift (φ.comp $ ι _ _) $
by { simp only [← comp_assoc, ← hf, ← hg], simp only [comp_assoc, condition] }

variables {φ : normed_group_hom V₁ V₂} {ψ : normed_group_hom W₁ W₂}
variables {φ' : normed_group_hom V₂ V₃} {ψ' : normed_group_hom W₂ W₃}

@[simp] lemma map_ι (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) :
  (ι f₂ g₂).comp (map φ ψ hf hg) = φ.comp (ι _ _) :=
lift_ι _ _

@[simp] lemma map_id : @map _ _ _ _ _ _ _ _ f₁ g₁ f₁ g₁ id id rfl rfl = id :=
by { ext, refl }

lemma comm_sq₂ (hf : ψ.comp f₁ = f₂.comp φ)(hf' : ψ'.comp f₂ = f₃.comp φ') :
  (ψ'.comp ψ).comp f₁ = f₃.comp (φ'.comp φ) :=
by rw [comp_assoc, hf, ← comp_assoc, hf', comp_assoc]

lemma map_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  (hf' : ψ'.comp f₂ = f₃.comp φ') (hg' : ψ'.comp g₂ = g₃.comp φ') :
  (map φ' ψ' hf' hg').comp (map φ ψ hf hg) =
    map (φ'.comp φ) (ψ'.comp ψ) (comm_sq₂ hf hf') (comm_sq₂ hg hg') :=
by { ext, refl }

lemma ι_norm_noninc : (ι f g).norm_noninc := λ v, le_rfl

lemma lift_norm_noninc (φ : normed_group_hom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.norm_noninc) :
  (lift φ h).norm_noninc :=
hφ

lemma lift_bound_by (φ : normed_group_hom V₁ V) (h : f.comp φ = g.comp φ)
  (C : ℝ≥0) (hφ : φ.bound_by C) :
  (lift φ h).bound_by C :=
hφ

lemma norm_lift_le (φ : normed_group_hom V₁ V) (h : f.comp φ = g.comp φ)
  (C : ℝ≥0) (hφ : ∥φ∥ ≤ C) :
  ∥(lift φ h)∥ ≤ C :=
hφ

lemma map_norm_noninc (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  (hφ : φ.norm_noninc) :
  (map φ ψ hf hg).norm_noninc :=
lift_norm_noninc _ _ $ hφ.comp ι_norm_noninc

lemma map_bound_by (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  (C : ℝ≥0) (hφ : (φ.comp (ι f₁ g₁)).bound_by C) :
  (map φ ψ hf hg).bound_by C :=
lift_bound_by _ _ _ hφ

lemma norm_map_le (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  (C : ℝ≥0) (hφ : ∥φ.comp (ι f₁ g₁)∥ ≤ C) :
  ∥map φ ψ hf hg∥ ≤ C :=
norm_lift_le _ _ _ hφ

end equalizer

end normed_group_hom
