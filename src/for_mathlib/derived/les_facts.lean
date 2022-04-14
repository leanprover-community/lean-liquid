import for_mathlib.derived.example

.

noncomputable theory

universes v u

open category_theory category_theory.triangulated homotopy_category opposite
open bounded_homotopy_category

variables {C : Type u} [category.{v} C] [abelian C] [enough_projectives C]

namespace bounded_homotopy_category

variables (i : ℤ) (A : triangle (bounded_homotopy_category C)) (B : bounded_homotopy_category C)

def Ext.map₁ : ((Ext i).obj (op A.obj₂)).obj B ⟶ ((Ext i).obj (op A.obj₁)).obj B :=
((Ext i).map A.mor₁.op).app B

def Ext.map₂ : ((Ext i).obj (op A.obj₃)).obj B ⟶ ((Ext i).obj (op A.obj₂)).obj B :=
((Ext i).map A.mor₂.op).app B

def Ext.shift_neg_iso (A B : bounded_homotopy_category C) :
  ((Ext i).obj (op (A⟦(-1:ℤ)⟧))).obj B ≅ ((Ext (i + 1)).obj (op A)).obj B :=
sorry

def Ext.shift_iso (A B : bounded_homotopy_category C) :
  ((Ext i).obj (op A)).obj B ≅ ((Ext (i + 1)).obj (op (A⟦(1:ℤ)⟧))).obj B :=
sorry

def Ext.δ :
  ((Ext i).obj (op A.obj₁)).obj B ⟶ ((Ext (i+1)).obj (op A.obj₃)).obj B :=
(Ext.shift_iso i A.obj₁ B).hom ≫ ((Ext (i + 1)).map A.mor₃.op).app B

set_option pp.universes true

-- this should be true up to a possible minus sign
lemma Ext.δ_aux :
  Ext.δ i A B =
  ((Ext i).map A.inv_rotate.mor₁.op).app B ≫ (Ext.shift_neg_iso i A.obj₃ B).hom :=
sorry

lemma Ext.five_term_exact_seq (hA : A ∈ dist_triang (bounded_homotopy_category C)) :
  exact_seq Ab.{v} [Ext.map₂ i A B, Ext.map₁ i A B, Ext.δ i A B, Ext.map₂ (i+1) A B] :=
begin
  refine exact.cons _ (exact.cons _ (exact.exact_seq _)),
  { exact (four_term_exact_seq ((Ext i).flip.obj B).right_op A hA).pair.unop, },
  { rw [Ext.δ_aux, exact_comp_iso],
    exact (five_term_exact_seq ((Ext i).flip.obj B).right_op A hA).pair.unop, },
  { rw [Ext.δ, exact_iso_comp],
    exact (four_term_exact_seq ((Ext (i+1)).flip.obj B).right_op A hA).unop.pair, }
end

end bounded_homotopy_category

namespace bounded_homotopy_category

section cone

variables {A B : cochain_complex C ℤ} (f : A ⟶ B)
variables [is_bounded_above ⟨A⟩] [is_bounded_above ⟨B⟩]

def cone :
  bounded_homotopy_category C :=
{ val := { as := homological_complex.cone f },
  bdd := begin
    obtain ⟨a, ha⟩ := is_bounded_above.cond ⟨A⟩,
    obtain ⟨b, hb⟩ := is_bounded_above.cond ⟨B⟩,
    refine ⟨⟨max a b, _⟩⟩,
    intros i hi,
    specialize ha (i+1) ((le_max_left _ _).trans $ hi.trans $ by norm_num),
    specialize hb i ((le_max_right _ _).trans $ hi),
    dsimp,
    constructor,
    { intros Y g, ext,
      { exact ha.eq_of_src _ _ },
      { exact hb.eq_of_src _ _ }, },
    { intros Y g, ext,
      { exact ha.eq_of_tgt _ _ },
      { exact hb.eq_of_tgt _ _ }, }
  end }

def cone.in : bounded_homotopy_category.mk ⟨B⟩ ⟶ cone f :=
(homotopy_category.quotient _ _).map (homological_complex.cone.in f)

-- move me
instance is_bounded_above_shift (i : ℤ) : is_bounded_above {as := A⟦i⟧} :=
begin
  obtain ⟨a, ha⟩ := is_bounded_above.cond ⟨A⟩,
  refine ⟨⟨a - i, _⟩⟩,
  intros j hj,
  rw sub_le_iff_le_add at hj,
  exact ha (j + i) hj,
end

def cone.out : cone f ⟶ bounded_homotopy_category.mk ⟨A⟦(1:ℤ)⟧⟩ :=
(homotopy_category.quotient _ _).map (homological_complex.cone.out f)

def cone.triangle : triangle (bounded_homotopy_category C) :=
{ obj₁ := bounded_homotopy_category.mk ⟨A⟩,
  obj₂ := bounded_homotopy_category.mk ⟨B⟩,
  obj₃ := cone f,
  mor₁ := (homotopy_category.quotient _ _).map f,
  mor₂ := cone.in f,
  mor₃ := cone.out f }

lemma cone.triangle_dist :
  (neg₃_functor _).obj (cone.triangle f) ∈ dist_triang (bounded_homotopy_category C) :=
(cone_triangleₕ_mem_distinguished_triangles _ _ f)

end cone

end bounded_homotopy_category

section
-- these should already be there for `Ext`, so it shouldn't be too hard

-- move me
instance Ext'.flip_additive (i : ℤ) (B : C) : ((Ext' i).flip.obj B).additive :=
sorry

-- move me
instance Ext'.additive (i : ℤ) (A : Cᵒᵖ) : ((Ext' i).obj A).additive :=
sorry

end

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
  (sq₁ : f₁ ≫ α₂ = α₁ ≫ g₁) (sq₂ : f₂ ≫ α₃ = α₂ ≫ g₂)
  (Z : C) (hf : short_exact f₁ f₂) (hg : short_exact g₁ g₂)
  (H : ∀ i, is_iso (((Ext' i).map α₃.op).app Z)) :
  (epi (((Ext' 0).map α₁.op).app Z) ∧ ∀ i > 0, is_iso (((Ext' i).map α₁.op).app Z)) ↔
  (epi (((Ext' 0).map α₂.op).app Z) ∧ ∀ i > 0, is_iso (((Ext' i).map α₂.op).app Z)) :=
sorry
