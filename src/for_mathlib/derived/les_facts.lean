import for_mathlib.derived.example

.

noncomputable theory

universes v u

open category_theory homotopy_category opposite

variables {C : Type u} [category.{v} C] [abelian C] [enough_projectives C]

lemma is_zero_iff_epi_and_is_iso
  {A₁ A₂ A₃ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (B : C) (h : short_exact f g) :
  (∀ i > 0, is_zero (((Ext' i).obj (op A₃)).obj B)) ↔
  (epi (((Ext' 0).map f.op).app B) ∧ ∀ i > 0, is_iso (((Ext' i).map f.op).app B)) :=
sorry

lemma epi_and_is_iso_iff_of_is_iso
  {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
  (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
  (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)
  (α₁ : X₁ ⟶ Y₁) (α₂ : X₂ ⟶ Y₂) (α₃ : X₃ ⟶ Y₃)
  (Z : C) (hf : short_exact f₁ f₂) (hg : short_exact g₁ g₂)
  (H : ∀ i, is_iso (((Ext' i).map α₃.op).app Z)) :
  (epi (((Ext' 0).map α₁.op).app Z) ∧ ∀ i > 0, is_iso (((Ext' i).map α₁.op).app Z)) ↔
  (epi (((Ext' 0).map α₂.op).app Z) ∧ ∀ i > 0, is_iso (((Ext' i).map α₂.op).app Z)) :=
sorry
