import category_theory.triangulated.pretriangulated
import for_mathlib.homological_complex_shift

noncomputable theory

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v u

namespace category_theory.triangulated
open category_theory.category

variables (C : Type u) [category.{v} C] [preadditive C]
variables [has_shift C ℤ]

local attribute [instance, reducible] endofunctor_monoidal_category

namespace triangle

@[simps]
def triangle_shift_obj (T : triangle C) (i : ℤ) : triangle C :=
triangle.mk C
  (i.neg_one_pow • ((shift_functor _ i).map T.mor₁))
  (i.neg_one_pow • (((shift_functor _ i).map T.mor₂)))
  (i.neg_one_pow • ((shift_functor C i).map T.mor₃ ≫ (shift_comm _ _ _).hom))

@[simps]
def triangle_shift_map {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) :
  triangle_shift_obj C T₁ i ⟶ triangle_shift_obj C T₂ i :=
{ hom₁ := (shift_functor _ i).map f.hom₁,
  hom₂ := (shift_functor _ i).map f.hom₂,
  hom₃ := (shift_functor _ i).map f.hom₃,
  comm₁' := by { dsimp, simp only [functor.map_zsmul,
    preadditive.zsmul_comp, preadditive.comp_zsmul, ← functor.map_comp, f.comm₁] },
  comm₂' := by { dsimp, simp only [functor.map_zsmul,
    preadditive.zsmul_comp, preadditive.comp_zsmul, ← functor.map_comp, f.comm₂] },
  comm₃' := begin
    dsimp,
    simp only [functor.map_zsmul,
      preadditive.zsmul_comp, preadditive.comp_zsmul],
    congr' 1,
    simp only [ shift_comm_hom_comp, assoc, iso.cancel_iso_hom_right_assoc,
      ← functor.map_comp, f.comm₃],
  end }

@[simps]
def triangle_shift_functor (i : ℤ) : triangle C ⥤ triangle C :=
{ obj := λ T, triangle_shift_obj C T i,
  map := λ T₁ T₂ f, triangle_shift_map C f _,
  map_id' := begin
    intros T,
    ext,
    all_goals { dsimp, simp },
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    ext,
    all_goals { dsimp, simp },
  end, } .

variable {C}

@[simps]
def iso.of_components {T₁ T₂ : triangle C}
  (e₁ : T₁.obj₁ ≅ T₂.obj₁)
  (e₂ : T₁.obj₂ ≅ T₂.obj₂)
  (e₃ : T₁.obj₃ ≅ T₂.obj₃) (h₁ h₂ h₃) : T₁ ≅ T₂ :=
{ hom :=
  { hom₁ := e₁.hom,
    hom₂ := e₂.hom,
    hom₃ := e₃.hom,
    comm₁' := h₁,
    comm₂' := h₂,
    comm₃' := h₃ },
  inv :=
  { hom₁ := e₁.inv,
    hom₂ := e₂.inv,
    hom₃ := e₃.inv,
    comm₁' := by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, h₁],
    comm₂' := by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, h₂],
    comm₃' := by rw [← functor.map_iso_inv, iso.comp_inv_eq, category.assoc, iso.eq_inv_comp,
      functor.map_iso_hom, h₃], },
  hom_inv_id' := by ext; dsimp; simp,
  inv_hom_id' := by ext; dsimp; simp }
.

variable (C)

@[simps]
def triangle_shift_functor_ε : 𝟭 (triangulated.triangle C) ≅ triangle_shift_functor C 0 :=
nat_iso.of_components (λ T,
  iso.of_components
    (shift_zero _ _).symm
    (shift_zero _ _).symm
    (shift_zero _ _).symm
    sorry -- use ((shift_functor_zero _ _).inv.naturality _)
    sorry -- use ((shift_functor_zero _ _).inv.naturality _)
    begin
      dsimp,
      rw one_smul,
      rw ← nat_trans.naturality_assoc, dsimp [shift_comm],
      simp only [obj_ε_app, discrete.functor_map_id, nat_trans.id_app, ε_app_obj, assoc, id_comp],
      rw [← nat_trans.comp_app, ← nat_trans.comp_app],
      erw [monoidal_functor.μ_inv_hom_id_assoc, id_comp], refl,
    end)
  begin
    intros T₁ T₂ f, ext;
    { dsimp only [triangle_morphism.comp_hom₁, iso.of_components_hom_hom₁, triangle_shift_map_hom₁,
        triangle_morphism.comp_hom₂, iso.of_components_hom_hom₂, triangle_shift_map_hom₂,
        triangle_morphism.comp_hom₃, iso.of_components_hom_hom₃, triangle_shift_map_hom₃,
        functor.id_map, triangle_category_comp, iso.symm_hom, iso.app_inv, iso.symm_inv,
        monoidal_functor.ε_iso_hom, triangle_shift_functor_map],
      rw ← nat_trans.naturality _ _, refl },
  end
.

@[simps]
def triangle_shift_functor_μ (i j : ℤ) : triangle_shift_functor C i ⋙ triangle_shift_functor C j ≅
    triangle_shift_functor C (i + j) :=
nat_iso.of_components (λ T,
  iso.of_components
    (shift_add _ _ _).symm
    (shift_add _ _ _).symm
    (shift_add _ _ _).symm
    sorry -- use ((shift_functor_add _ _ _).inv.naturality _ )
    sorry -- use ((shift_functor_add _ _ _).inv.naturality _ )
    begin
      /-
      dsimp,
      rw ← nat_trans.naturality_assoc,
      simp only [functor.map_comp, assoc, obj_μ_app, functor.comp_map],
      congr' 1,
      rw [← nat_trans.comp_app, ← nat_trans.comp_app],
      -/
      sorry
    end)
  begin
    intros T₁ T₂ f, ext;
    { dsimp only [triangle_morphism.comp_hom₁, iso.of_components_hom_hom₁, triangle_shift_map_hom₁,
        triangle_morphism.comp_hom₂, iso.of_components_hom_hom₂, triangle_shift_map_hom₂,
        triangle_morphism.comp_hom₃, iso.of_components_hom_hom₃, triangle_shift_map_hom₃,
        functor.id_map, triangle_category_comp, iso.symm_hom, iso.app_inv, iso.symm_inv,
        monoidal_functor.ε_iso_hom, triangle_shift_functor_map],
      rw ← nat_trans.naturality _ _, refl },
  end

def triangle_shift_core : shift_mk_core (triangle C) ℤ :=
{ F := triangle_shift_functor _,
  ε := triangle_shift_functor_ε _,
  μ := λ i j, triangle_shift_functor_μ _ _ _,
  associativity := sorry,
  left_unitality := sorry,
  right_unitality := sorry }

instance : has_shift (triangle C) ℤ :=
has_shift_mk _ _ $ triangle_shift_core _

@[simp]
lemma shift_obj₁ (T : triangle C) (i : ℤ) : T⟦i⟧.obj₁ = T.obj₁⟦i⟧ := rfl

@[simp]
lemma shift_obj₂ (T : triangle C) (i : ℤ) : T⟦i⟧.obj₂ = T.obj₂⟦i⟧ := rfl

@[simp]
lemma shift_obj₃ (T : triangle C) (i : ℤ) : T⟦i⟧.obj₃ = T.obj₃⟦i⟧ := rfl

@[simp]
lemma shift_mor₁ (T : triangle C) (i : ℤ) : T⟦i⟧.mor₁ = i.neg_one_pow • T.mor₁⟦i⟧' := rfl

@[simp]
lemma shift_mor₂ (T : triangle C) (i : ℤ) : T⟦i⟧.mor₂ = i.neg_one_pow • T.mor₂⟦i⟧' := rfl

@[simp]
lemma shift_mor₃ (T : triangle C) (i : ℤ) :
  T⟦i⟧.mor₃ = i.neg_one_pow • (T.mor₃⟦i⟧' ≫ (shift_comm _ _ _).hom) := rfl

@[simp]
lemma shift_hom₁ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₁ = f.hom₁⟦i⟧' := rfl

@[simp]
lemma shift_hom₂ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₂ = f.hom₂⟦i⟧' := rfl

@[simp]
lemma shift_hom₃ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₃ = f.hom₃⟦i⟧' := rfl

end triangle

/-
instance {C : Type*} [category C] [preadditive C] (X Y : C) : has_neg (X ≅ Y) :=
⟨λ f,
{ hom := -f.hom,
  inv := -f.inv,
  hom_inv_id' := by simp only [comp_neg, neg_comp, iso.hom_inv_id, neg_neg],
  inv_hom_id' := by simp only [comp_neg, neg_comp, iso.inv_hom_id, neg_neg] }⟩

@[simp] lemma _root_.category_theory.neg_hom
   {C : Type*} [category C] [preadditive C] {X Y : C} (f : X ≅ Y) :
   (-f).hom = -(f.hom) := rfl

@[simp] lemma _root_.category_theory.neg_inv
   {C : Type*} [category C] [preadditive C] {X Y : C} (f : X ≅ Y) :
   (-f).inv = -(f.inv) := rfl
-/

namespace pretriangulated
variables [has_zero_object C] [∀ (i : ℤ), (shift_functor C i).additive] [pretriangulated C]

lemma shift_of_dist_triangle (T : triangle C) (hT : T ∈ dist_triang C) (i : ℤ) :
  T⟦i⟧ ∈ dist_triang C :=
begin
  induction i using int.induction_on with i IH i IH,
  { exact isomorphic_distinguished T hT _ (shift_zero _ _), },
  { suffices : T⟦(i+1 : ℤ)⟧ ≅ T⟦(i:ℤ)⟧.rotate.rotate.rotate,
    { refine isomorphic_distinguished _ _ _ this,
      repeat { refine rot_of_dist_triangle _ _ _ },
      exact IH },
    refine shift_add _ _ _ ≪≫ _,
    refine triangle.iso.of_components (iso.refl _) (iso.refl _) (iso.refl _) _ _ _,
    { dsimp, simp only [category.id_comp, category.comp_id, comp_neg, neg_one_smul], },
    { dsimp, simp only [category.id_comp, category.comp_id, neg_comp, neg_one_smul], },
    { dsimp, simp only [category.id_comp, category.comp_id, neg_comp, neg_one_smul],
      simp only [functor.map_comp, assoc, category_theory.functor.map_id, comp_id,
        functor.map_zsmul, preadditive.zsmul_comp, preadditive.comp_zsmul],
      congr' 2,
      sorry }, },
  sorry
end

end pretriangulated

end category_theory.triangulated
