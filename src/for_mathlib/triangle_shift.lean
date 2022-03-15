import category_theory.triangulated.pretriangulated

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

-- TODO(?): add `(-1)^i` so that the signs in the morphisms
-- in `T⟦1⟧` matches those of `T.rotate.rotate.rotate`.
@[simps]
def triangle_shift_obj (T : triangle C) (i : ℤ) : triangle C :=
triangle.mk C
  ((shift_functor _ i).map T.mor₁)
  (((shift_functor _ i).map T.mor₂))
  ((shift_functor C i).map T.mor₃ ≫ (shift_comm _ _ _).hom)

@[simps]
def triangle_shift_map {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) :
  triangle_shift_obj C T₁ i ⟶ triangle_shift_obj C T₂ i :=
{ hom₁ := (shift_functor _ i).map f.hom₁,
  hom₂ := (shift_functor _ i).map f.hom₂,
  hom₃ := (shift_functor _ i).map f.hom₃,
  comm₁' := by { dsimp, simp only [← functor.map_comp, f.comm₁] },
  comm₂' := by { dsimp, simp only [← functor.map_comp, f.comm₂] },
  comm₃' := begin
    dsimp,
    simp only [shift_comm_hom_comp, assoc, iso.cancel_iso_hom_right_assoc,
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
variable (C)

@[simps]
def triangle_shift_functor_ε : 𝟭 (triangulated.triangle C) ≅ triangle_shift_functor C 0 :=
nat_iso.of_components (λ T,
  iso.of_components
    (shift_zero _ _).symm
    (shift_zero _ _).symm
    (shift_zero _ _).symm
    ((shift_functor_zero _ _).inv.naturality _)
    ((shift_functor_zero _ _).inv.naturality _)
    begin
      dsimp, rw ← nat_trans.naturality_assoc, dsimp [shift_comm],
      simp only [obj_ε_app, discrete.functor_map_id, nat_trans.id_app, ε_app_obj, assoc, id_comp],
      rw [← nat_trans.comp_app, ← nat_trans.comp_app],
      erw [monoidal_functor.μ_inv_hom_id_assoc, id_comp], refl,
    end)
  sorry

@[simps]
def triangle_shift_functor_μ (i j : ℤ) : triangle_shift_functor C i ⋙ triangle_shift_functor C j ≅
    triangle_shift_functor C (i + j) :=
nat_iso.of_components (λ T,
  iso.of_components
    (shift_add _ _ _).symm
    (shift_add _ _ _).symm
    (shift_add _ _ _).symm
    ((shift_functor_add _ _ _).inv.naturality _ )
    ((shift_functor_add _ _ _).inv.naturality _ )
    sorry)
  sorry

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
lemma shift_mor₁ (T : triangle C) (i : ℤ) : T⟦i⟧.mor₁ = T.mor₁⟦i⟧' := rfl

@[simp]
lemma shift_mor₂ (T : triangle C) (i : ℤ) : T⟦i⟧.mor₂ = T.mor₂⟦i⟧' := rfl

@[simp]
lemma shift_mor₃ (T : triangle C) (i : ℤ) : T⟦i⟧.mor₃ = T.mor₃⟦i⟧' ≫ (shift_comm _ _ _).hom := rfl

@[simp]
lemma shift_hom₁ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₁ = f.hom₁⟦i⟧' := rfl

@[simp]
lemma shift_hom₂ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₂ = f.hom₂⟦i⟧' := rfl

@[simp]
lemma shift_hom₃ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₃ = f.hom₃⟦i⟧' := rfl

end triangle

namespace pretriangulated
variables [has_zero_object C] [∀ (i : ℤ), (shift_functor C i).additive] [pretriangulated C]

lemma shift_of_dist_triangle (T : triangle C) (hT : T ∈ dist_triang C) (i : ℤ) :
  T⟦i⟧ ∈ dist_triang C := sorry

end pretriangulated

end category_theory.triangulated
