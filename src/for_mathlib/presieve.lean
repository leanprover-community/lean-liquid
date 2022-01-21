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

noncomputable theory

def index_of_arrows {ι} {B Y} {X : ι → C} {f : Π i, X i ⟶ B} {g : Y ⟶ B}
  (h : of_arrows X f g) : ι :=
((mem_of_arrows_iff X f g).mp h).some

def eq_obj_of_arrows {ι} {B Y} {X : ι → C} {f : Π i, X i ⟶ B} {g : Y ⟶ B}
  (h : of_arrows X f g) : Y = X (index_of_arrows h) :=
((mem_of_arrows_iff X f g).mp h).some_spec.some

lemma eq_hom_ofarrows {ι} {B Y} {X : ι → C} {f : Π i, X i ⟶ B} {g : Y ⟶ B}
  (h : of_arrows X f g) : g = eq_to_hom (eq_obj_of_arrows h) ≫ f _ :=
((mem_of_arrows_iff X f g).mp h).some_spec.some_spec

def mk_family_of_elements_of_arrows {ι} {B} (X : ι → C) (f : Π i, X i ⟶ B)
  (F : Cᵒᵖ ⥤ Type w) (x : Π i, F.obj (op (X i))) :
  (of_arrows X f).family_of_elements F := λ Y f hf,
F.map (eq_to_hom $ eq_obj_of_arrows hf).op (x $ index_of_arrows hf)

lemma mk_family_of_elements_of_arrows_compatible
  {ι} {B} (X : ι → C) (f : Π i, X i ⟶ B)
  (F : Cᵒᵖ ⥤ Type w) (x : Π i, F.obj (op (X i)))
  (hx : ∀ (i j : ι) Z (g₁ : Z ⟶ X i) (g₂ : Z ⟶ X j),
    F.map g₁.op (x _) = F.map g₂.op (x _)) :
  (mk_family_of_elements_of_arrows X f F x).compatible :=
begin
  intros X Y Z g₁ g₂ f₁ f₂ h₁ h₂ h,
  dsimp [mk_family_of_elements_of_arrows],
  specialize hx (index_of_arrows h₁) (index_of_arrows h₂) Z
    (g₁ ≫ eq_to_hom (eq_obj_of_arrows h₁))
    (g₂ ≫ eq_to_hom (eq_obj_of_arrows h₂)),
  convert hx using 1; simp,
end

@[simp]
lemma mk_family_of_elements_of_arrows_eval
  {ι} {B} (X : ι → C) (f : Π i, X i ⟶ B)
  (F : Cᵒᵖ ⥤ Type w) (x : Π i, F.obj (op (X i)))
  (hx : ∀ (i j : ι) Z (g₁ : Z ⟶ X i) (g₂ : Z ⟶ X j),
    F.map g₁.op (x _) = F.map g₂.op (x _)) (i : ι) :
  (mk_family_of_elements_of_arrows X f F x) (f i) (presieve.of_arrows.mk i) = x i :=
begin
  have : X i = X (index_of_arrows (presieve.of_arrows.mk i)),
  { fapply eq_obj_of_arrows },
  rotate 2, exact f,
  dsimp [mk_family_of_elements_of_arrows],
  specialize hx i (index_of_arrows (presieve.of_arrows.mk i)),
  rotate 3, exact X, exact f,
  specialize hx (X i) (𝟙 _) (eq_to_hom this),
  simp at hx,
  simpa using hx.symm,
end

end category_theory.presieve
