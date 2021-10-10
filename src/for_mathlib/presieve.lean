import category_theory.sites.sheaf

open category_theory opposite

universes w v u v' u'

variables {C : Type u} [category.{v} C]

namespace category_theory.presieve

lemma mem_of_arrows_iff {ι} {B Y} (X : ι → C) (f : Π i, X i ⟶ B) (g : Y ⟶ B) :
  of_arrows X f g ↔ ∃ (i : ι) (hi : Y = X i), g = eq_to_hom hi ≫ f i :=
begin
  split,
  { rintros ⟨i⟩,
    use [i, rfl],
    simp },
  { rintros ⟨i,rfl,rfl⟩,
    simp [of_arrows.mk i] }
end

-- Below is a temporary fix to the unnecessary universe restrictions...
-- eventually, this should be fixed in mathlib.

def family_of_elements' {X : C} (R : presieve X) (P : Cᵒᵖ ⥤ Type w) :=
Π ⦃Y : C⦄ (f : Y ⟶ X), R f → P.obj (op Y)

variables {X : C} {R : presieve X} {P : Cᵒᵖ ⥤ Type w}

def family_of_elements'.compatible (x : R.family_of_elements' P) : Prop :=
∀ ⦃Y₁ Y₂ Z⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄
  (h₁ : R f₁) (h₂ : R f₂), g₁ ≫ f₁ = g₂ ≫ f₂ → P.map g₁.op (x f₁ h₁) = P.map g₂.op (x f₂ h₂)

def family_of_elements'.is_amalgamation (x : R.family_of_elements' P) (t : P.obj (op X)) : Prop :=
∀ ⦃Y : C⦄ (f : Y ⟶ X) (h : R f), P.map f.op t = x f h

def is_sheaf_for' (R : presieve X) (P : Cᵒᵖ ⥤ Type w) : Prop :=
∀ (x : R.family_of_elements' P), x.compatible → ∃! t, x.is_amalgamation t

def is_sheaf' (P : Cᵒᵖ ⥤ Type w) (J : grothendieck_topology C) : Prop :=
∀ ⦃X⦄ (S : sieve X), S ∈ J X → is_sheaf_for' S P

end category_theory.presieve
