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

namespace category_theory.presheaf

variables {D : Type u'} [category.{v'} D]

def is_sheaf'' (P : Cᵒᵖ ⥤ D) (J : grothendieck_topology C) : Prop :=
∀ (T : D), category_theory.presieve.is_sheaf' (P ⋙ coyoneda.obj (op T)) J

lemma is_sheaf''_def (P : Cᵒᵖ ⥤ D) (J : grothendieck_topology C) :
  is_sheaf'' P J ↔
  ∀ (T : D), category_theory.presieve.is_sheaf' (P ⋙ coyoneda.obj (op T)) J := iff.rfl

end category_theory.presheaf

namespace category_theory

@[derive category]
def Sheaf' (J : grothendieck_topology C) (D : Type u') [category.{v'} D] :=
{ F : Cᵒᵖ ⥤ D // presheaf.is_sheaf'' F J }

variables (J : grothendieck_topology C) (D : Type u') [category.{v'} D]

@[derive [full, faithful]]
def Sheaf'_to_presheaf : Sheaf' J D ⥤ Cᵒᵖ ⥤ D :=
full_subcategory_inclusion _

@[simps obj map]
def Sheaf'_to_Sheaf (D : Type u') [category.{v} D] : Sheaf' J D ⥤ Sheaf J D :=
{ obj := λ F, ⟨F.1, F.2⟩,
  map := λ F G η, η }

@[simps obj map]
def Sheaf_to_Sheaf' (D : Type u') [category.{v} D] : Sheaf J D ⥤ Sheaf' J D :=
{ obj := λ F, ⟨F.1, F.2⟩,
  map := λ F G η, η }

@[simps functor inverse]
def Sheaf'_equiv_Sheaf (D : Type u') [category.{v} D] : Sheaf' J D ≌ Sheaf J D :=
{ functor := Sheaf'_to_Sheaf _ _,
  inverse := Sheaf_to_Sheaf' _ _,
  unit_iso := nat_iso.of_components (λ F, eq_to_iso (by { cases F, refl })) begin
    rintros ⟨F,hF⟩ ⟨G,hG⟩ η,
    ext,
    dsimp,
    simp,
  end,
  counit_iso := nat_iso.of_components (λ F, eq_to_iso (by { cases F, refl })) begin
    rintros ⟨F,hF⟩ ⟨G,hG⟩ η,
    ext,
    dsimp,
    simp,
  end,
  functor_unit_iso_comp' := begin
    rintros ⟨F,hF⟩,
    ext,
    dsimp,
    simp,
  end }

end category_theory
