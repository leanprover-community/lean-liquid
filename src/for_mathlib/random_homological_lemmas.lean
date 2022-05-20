
import for_mathlib.short_exact
import for_mathlib.derived.defs

noncomputable theory

open category_theory category_theory.limits

variables {A : Type*} [category A] [abelian A] [enough_projectives A]
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

-- this files exists to save these lemmas from a file that will probably get nuked

-- move me
lemma biprod.lift_desc_comm {X₁ X₂ Y₁ Y₂ : A}
  (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
  biprod.lift (biprod.desc f₁₁ f₂₁) (biprod.desc f₁₂ f₂₂) =
  biprod.desc (biprod.lift f₁₁ f₁₂) (biprod.lift f₂₁ f₂₂) :=
by ext; simp only [category.assoc,
  biprod.lift_fst, biprod.lift_snd, biprod.inl_desc, biprod.inr_desc]

-- move me
lemma biprod.comp_lift {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (h : X ⟶ Z) :
  f ≫ biprod.lift g h = biprod.lift (f ≫ g) (f ≫ h) :=
by ext; simp only [category.assoc, biprod.lift_fst, biprod.lift_snd]

-- move me
@[reassoc]
lemma comp_factor_thru_image_eq_zero {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  f ≫ factor_thru_image g = 0 :=
by rw [← cancel_mono (limits.image.ι g), category.assoc, limits.image.fac, w, zero_comp]
