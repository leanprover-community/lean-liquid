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

def horseshoe_step (A : short_exact_sequence C) : short_exact_sequence C :=
{ fst := projective.over A.1,
  snd := (projective.over A.1) ⊞ (projective.over A.3),
  trd := projective.over A.3,
  f := biprod.inl,
  g := biprod.snd,
  mono := infer_instance,
  epi := infer_instance,
  exact := infer_instance }



end short_exact_sequence
