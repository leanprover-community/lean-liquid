import category_theory.closed.monoidal
import category_theory.monoidal.braided
import tactic

namespace category_theory.monoidal

open category_theory
open category_theory.monoidal_category

universes v u
variables {C : Type u} [category.{v} C] [monoidal_category.{v} C]

class right_closed (X : C) :=
(is_adj : is_left_adjoint (tensor_right X))

attribute [instance, priority 100] right_closed.is_adj

variable (C)

class monoidal_closed_right :=
(closed : Π (X : C), right_closed X)

attribute [instance, priority 100] monoidal_closed_right.closed

variable [monoidal_closed_right.{v} C]

variable {C}

def internal_hom (X Y : C) : C :=
(right_adjoint (tensor_right X)).obj Y

def internal_hom_equiv (X Y Z : C) :
  (X ⊗ Y ⟶ Z) ≃ (X ⟶ internal_hom Y Z) :=
(adjunction.of_left_adjoint (tensor_right Y)).hom_equiv X Z

def internal_hom_postcompose (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
  internal_hom X Y₁ ⟶ internal_hom X Y₂ :=
(right_adjoint (tensor_right X)).map f

@[simp]
lemma internal_hom_postcompose_id (X Y : C) :
  internal_hom_postcompose X (𝟙 Y) = 𝟙 _ :=
(right_adjoint (tensor_right X)).map_id _

@[simp]
lemma internal_hom_postcompose_comp (X : C) {Y₁ Y₂ Y₃ : C} (f₁ : Y₁ ⟶ Y₂) (f₂ : Y₂ ⟶ Y₃) :
  internal_hom_postcompose X (f₁ ≫ f₂) =
  internal_hom_postcompose X f₁ ≫ internal_hom_postcompose X f₂ :=
(right_adjoint (tensor_right X)).map_comp _ _

def internal_hom_precompose {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
  internal_hom X₂ Y ⟶ internal_hom X₁ Y :=
(internal_hom_equiv _ _ _) $ (tensor_hom (𝟙 _) f ≫ (internal_hom_equiv _ _ _).symm (𝟙 _))

lemma split_left {A₁ A₂ B₁ B₂ : C} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
  (f ⊗ g) = (f ⊗ 𝟙 _) ≫ (𝟙 _ ⊗ g) := by simp

lemma split_right {A₁ A₂ B₁ B₂ : C} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
  (f ⊗ g) = (𝟙 _ ⊗ g) ≫ (f ⊗ 𝟙 _) := by simp

lemma internal_hom_equiv_tensor_right {X Y₁ Y₂ Z : C} (f : Y₁ ⟶ Y₂) (g : X ⊗ Y₂ ⟶ Z) :
  internal_hom_equiv _ _ _ ((𝟙 _ ⊗ f) ≫ g)  =
  internal_hom_equiv _ _ _ g ≫ internal_hom_precompose f _ :=
begin
  apply_fun (internal_hom_equiv _ _ _).symm,
  simp,
  dsimp [internal_hom_precompose, internal_hom_equiv, internal_hom],
  simp only [adjunction.hom_equiv_unit, adjunction.hom_equiv_counit, tensor_right_map,
    tensor_id,  adjunction.hom_equiv_naturality_right, functor.map_comp,
    category_theory.functor.map_id, category.id_comp, category.assoc,
    adjunction.hom_equiv_naturality_left_symm, adjunction.hom_equiv_naturality_right_symm],
  simp only [← tensor_right_map],
  rw (adjunction.of_left_adjoint (tensor_right Y₁)).counit_naturality_assoc,
  rw (adjunction.of_left_adjoint (tensor_right Y₁)).left_triangle_components_assoc,
  dsimp,
  simp only [← category.assoc, ← tensor_comp, category.id_comp, category.comp_id],
  conv_rhs { rw [split_right _ f, category.assoc] },
  rw ← tensor_right_map,
  simp only [functor.map_comp, category.assoc],
  rw (adjunction.of_left_adjoint (tensor_right Y₂)).counit_naturality,
  erw (adjunction.of_left_adjoint (tensor_right Y₂)).left_triangle_components_assoc,
end

@[simp]
lemma internal_hom_precompose_id (X Y : C) :
  internal_hom_precompose (𝟙 X) Y = 𝟙 _ :=
by { dsimp [internal_hom_precompose, internal_hom_equiv, internal_hom], simp, dsimp, simp }

@[simp]
lemma internal_hom_precompose_comp {X₁ X₂ X₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (Y : C) :
  internal_hom_precompose (f₁ ≫ f₂) Y =
  internal_hom_precompose f₂ Y ≫ internal_hom_precompose f₁ Y :=
begin
  change _ = internal_hom_equiv _ _ _ _ ≫ _,
  rw [← internal_hom_equiv_tensor_right, ← category.assoc, ← tensor_comp, category.id_comp],
  refl,
end

@[simp]
lemma internal_hom_postcompose_comp_precompose {A₁ A₂ B₁ B₂ : C}
  (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
  internal_hom_postcompose _ f ≫ internal_hom_precompose g _ =
  internal_hom_precompose g _ ≫ internal_hom_postcompose _ f :=
begin
  apply_fun (internal_hom_equiv _ _ _).symm,
  dsimp [internal_hom_precompose, internal_hom_postcompose, internal_hom_equiv, internal_hom],
  simp only [adjunction.hom_equiv_counit, tensor_right_map, tensor_id,
    adjunction.hom_equiv_naturality_right, adjunction.hom_equiv_unit, functor.map_comp,
    category_theory.functor.map_id, category.id_comp, category.assoc,
    adjunction.hom_equiv_naturality_left_symm, adjunction.hom_equiv_naturality_right_symm],
  simp only [← tensor_right_map, adjunction.counit_naturality, adjunction.counit_naturality_assoc,
    functor.map_comp, adjunction.left_triangle_components, adjunction.right_triangle_components,
    adjunction.left_triangle_components_assoc, adjunction.right_triangle_components_assoc],
  dsimp,
  simp only [← category.assoc, ← tensor_comp, category.id_comp, category.comp_id],
  rw [split_right _ g, category.assoc, ← tensor_right_map, adjunction.counit_naturality,
    category.assoc],
end

@[simps]
def internal_hom_functor : Cᵒᵖ ⥤ C ⥤ C :=
{ obj := λ X,
  { obj := λ Y, internal_hom X.unop Y,
    map := λ Y₁ Y₂, internal_hom_postcompose _ },
  map := λ X₁ X₂ f,
  { app := λ Y, internal_hom_precompose f.unop _ } }

end category_theory.monoidal
