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

-- move this
@[simp] def short_exact_sequence.mk_of_split (A B : C) : short_exact_sequence C :=
{ fst := A,
  snd := A ⊞ B,
  trd := B,
  f := biprod.inl,
  g := biprod.snd }

variables (A B : short_exact_sequence C) (f : A ⟶ B)

def horseshoe_base : short_exact_sequence C :=
short_exact_sequence.mk_of_split (projective.over A.1) (projective.over A.3)

def horseshoe_base_π : horseshoe_base A ⟶ A :=
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

instance epi_horseshoe_base_π_1 : epi (horseshoe_base_π A).1 :=
show epi (projective.π _), by apply_instance

variables {A B}

def horseshoe_ker [epi f.1] : short_exact_sequence C :=
(snake_input.mk_of_short_exact_sequence_hom _ _ _ f).kernel_sequence _
begin
  dsimp [snake_input.mk_of_short_exact_sequence_hom, snake_diagram.mk_of_short_exact_sequence_hom],
  rw snake_diagram.mk_functor_map_f1,
  exact A.mono',
end
begin
  sorry -- this sorry should follow from the `epi` assumption on `f.1`.
end

def horseshoe_ker_ι [epi f.1] : horseshoe_ker f ⟶ A :=
{ fst := kernel.ι _,
  snd := kernel.ι _,
  trd := kernel.ι _,
  sq1' :=
  begin
    dsimp [horseshoe_ker, snake_input.kernel_sequence,
      snake_input.mk_of_short_exact_sequence_hom, snake_diagram.mk_of_short_exact_sequence_hom],
    delta kernel.map,
    rw [snake_diagram.mk_functor_map_f0, kernel.lift_ι],
  end,
  sq2' :=
  begin
    dsimp [horseshoe_ker, snake_input.kernel_sequence,
      snake_input.mk_of_short_exact_sequence_hom, snake_diagram.mk_of_short_exact_sequence_hom],
    delta kernel.map,
    rw [snake_diagram.mk_functor_map_g0, kernel.lift_ι],
  end }
.

variables (A)

lemma horseshoe_ker_ι_comp_base_π :
  (horseshoe_ker_ι (horseshoe_base_π A)) ≫ horseshoe_base_π A = 0 :=
begin
  dsimp [horseshoe_ker_ι, horseshoe_base_π],
  ext1; show kernel.ι _ ≫ _ = 0; apply exact.w,
end

noncomputable
def horseshoe_step (A : short_exact_sequence C) :
  ℕ → Σ (X Y Z : short_exact_sequence C) (ι : X ⟶ Y), Y ⟶ Z
| 0     := ⟨horseshoe_ker (horseshoe_base_π A), _, _, horseshoe_ker_ι _, horseshoe_base_π _⟩
| (n+1) :=
⟨horseshoe_ker (horseshoe_base_π (horseshoe_step n).1), _, _, horseshoe_ker_ι _, horseshoe_base_π _⟩

@[reassoc] lemma horseshoe_step_comp_eq_zero :
  ∀ n, (horseshoe_step A n).2.2.2.1 ≫ (horseshoe_step A n).2.2.2.2 = 0
| 0     := horseshoe_ker_ι_comp_base_π _
| (n+1) := horseshoe_ker_ι_comp_base_π _

def horseshoe_obj (n : ℕ) := (horseshoe_step A n).2.1

def horseshoe_d (n : ℕ) : horseshoe_obj A (n+1) ⟶ horseshoe_obj A n :=
(horseshoe_step A (n+1)).2.2.2.2 ≫ eq_to_hom (by { dsimp [horseshoe_step], refl })
  ≫ (horseshoe_step A n).2.2.2.1

lemma horseshoe_d_d (n : ℕ) : horseshoe_d A (n+1) ≫ horseshoe_d A n = 0 :=
begin
  dsimp [horseshoe_d, horseshoe_ker_ι],
  simp only [category.id_comp, category.assoc, comp_zero, zero_comp,
    horseshoe_step_comp_eq_zero_assoc],
end

def horseshoe (A : short_exact_sequence C) : chain_complex (short_exact_sequence C) ℕ :=
chain_complex.of (horseshoe_obj A) (horseshoe_d A) (horseshoe_d_d A)

end short_exact_sequence
