import category_theory.derived
import data.matrix.notation

import for_mathlib.snake_lemma
import for_mathlib.short_exact_sequence

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace short_exact_sequence

variables {C : Type u} [category.{v} C] [abelian C] [enough_projectives C]

-- move this
lemma exact_of_split {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (χ : Z ⟶ Y) (φ : Y ⟶ X)
  (hfg : f ≫ g = 0) (H : φ ≫ f + g ≫ χ = 𝟙 Y) : exact f g :=
{ w := hfg,
  epi :=
  begin
    let ψ : (kernel_subobject g : C) ⟶ image_subobject f :=
      subobject.arrow _ ≫ φ ≫ factor_thru_image_subobject f,
    suffices : ψ ≫ image_to_kernel f g hfg = 𝟙 _,
    { convert epi_of_epi ψ _, rw this, apply_instance },
    rw ← cancel_mono (subobject.arrow _), swap, { apply_instance },
    simp only [image_to_kernel_arrow, image_subobject_arrow_comp, category.id_comp, category.assoc],
    calc (kernel_subobject g).arrow ≫ φ ≫ f
        = (kernel_subobject g).arrow ≫ 𝟙 Y : _
    ... = (kernel_subobject g).arrow        : category.comp_id _,
    rw [← H, preadditive.comp_add],
    simp only [add_zero, zero_comp, kernel_subobject_arrow_comp_assoc],
  end }

-- move this
instance exact_inl_snd (A B : C) : exact (biprod.inl : A ⟶ A ⊞ B) biprod.snd :=
exact_of_split _ _ biprod.inr biprod.fst biprod.inl_snd biprod.total

-- move this
def biprod_factors (A B : C) [projective A] [projective B]
  (E X : C) (f : A ⊞ B ⟶ X) (e : E ⟶ X) [epi e] :
  ∃ f' : A ⊞ B ⟶ E, f' ≫ e = f :=
⟨biprod.desc
  (projective.factor_thru (biprod.inl ≫ f) e)
  (projective.factor_thru (biprod.inr ≫ f) e),
  by ext; simp only [projective.factor_thru_comp, biprod.inl_desc_assoc, biprod.inr_desc_assoc]⟩

-- move this
instance projective_biprod (A B : C) [projective A] [projective B] : projective (A ⊞ B) :=
{ factors := λ E X f e he, by exactI biprod_factors A B E X f e }

def horseshoe_base (A : short_exact_sequence C) : short_exact_sequence C :=
{ fst := projective.over A.1,
  snd := (projective.over A.1) ⊞ (projective.over A.3),
  trd := projective.over A.3,
  f := biprod.inl,
  g := biprod.snd }

def horseshoe_base_π (A : short_exact_sequence C) : horseshoe_base A ⟶ A :=
{ fst := projective.π _,
  snd := biprod.desc (projective.π _ ≫ A.f) (projective.factor_thru (projective.π _) A.g),
  trd := projective.π _,
  sq1' := by { dsimp [horseshoe_base], simp only [biprod.inl_desc], },
  sq2' :=
  begin
    dsimp [horseshoe_base], apply category_theory.limits.biprod.hom_ext',
    { simp only [zero_comp, exact.w_assoc, biprod.inl_desc_assoc, category.assoc,
        short_exact_sequence.f_comp_g, comp_zero], },
    { simp only [projective.factor_thru_comp, biprod.inr_snd_assoc, biprod.inr_desc_assoc], }
  end }
.

def horseshoe_step {A B : short_exact_sequence C} (f : A ⟶ B) : short_exact_sequence C :=
{ fst := projective.syzygies f.1,
  snd := (projective.syzygies f.1) ⊞ (projective.syzygies f.3),
  trd := projective.syzygies f.3,
  f := biprod.inl,
  g := biprod.snd, }

def horseshoe_step_π {A B : short_exact_sequence C} (f : A ⟶ B) : horseshoe_step f ⟶ A :=
{ fst := projective.d _,
  snd := biprod.desc (projective.d _ ≫ A.f) (projective.factor_thru (projective.d _) A.g),
  trd := projective.d _,
  sq1' := by { dsimp [horseshoe_step], simp only [biprod.inl_desc], },
  sq2' :=
  begin
    dsimp [horseshoe_step], apply category_theory.limits.biprod.hom_ext',
    { simp only [zero_comp, exact.w_assoc, biprod.inl_desc_assoc, category.assoc,
        short_exact_sequence.f_comp_g, comp_zero], },
    { simp only [projective.factor_thru_comp, biprod.inr_snd_assoc, biprod.inr_desc_assoc], }
  end }
.

-- move this
attribute [instance] exact_d_f

-- move this
@[simp, reassoc] lemma projective_d_comp_self {A B : C} (f : A ⟶ B) : projective.d f ≫ f = 0 :=
exact.w

-- instance epi_horseshoe_step_π₁ {A B : short_exact_sequence C} (f : A ⟶ B) :
--   epi (horseshoe_step_π f).1 :=
-- show epi (projective.d _), from infer_instance

lemma horseshoe_step_π_comp_self {A B : short_exact_sequence C} (f : A ⟶ B) :
  horseshoe_step_π f ≫ f = 0 :=
begin
  apply category_theory.short_exact_sequence.hom.ext,
  { exact projective_d_comp_self f.1 },
  { show biprod.desc _ _ ≫ f.2 = 0, apply biprod.hom_ext',
    { simp only [biprod.inl_desc_assoc, category.assoc, ←f.sq1,
        zero_comp, comp_zero, exact.w_assoc], },
    { simp only [comp_zero, biprod.inr_desc_assoc], sorry /- jmc: this isn't provable -/ } },
  { exact projective_d_comp_self f.3 },
end

def horseshoe (A : short_exact_sequence C) : chain_complex (short_exact_sequence C) ℕ :=
sorry

end short_exact_sequence
