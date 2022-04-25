import for_mathlib.derived.example
import for_mathlib.derived.les2

.

noncomputable theory

universes v u

open category_theory category_theory.limits category_theory.triangulated homotopy_category opposite
open bounded_homotopy_category

variables {C : Type u} [category.{v} C] [abelian C] [enough_projectives C]

-- move me
instance is_bounded_above_shift {A : cochain_complex C ℤ} [is_bounded_above ⟨A⟩] (i : ℤ) :
  is_bounded_above {as := A⟦i⟧} :=
begin
  obtain ⟨a, ha⟩ := is_bounded_above.cond ⟨A⟩,
  refine ⟨⟨a - i, _⟩⟩,
  intros j hj,
  rw sub_le_iff_le_add at hj,
  exact ha (j + i) hj,
end

section

-- move me
instance homological_complex.single_additive (i : ℤ) :
  (homological_complex.single C (complex_shape.up ℤ) i).additive :=
{ map_add' := λ X Y f g, begin
    ext n, dsimp, by_cases hn : n = i,
    { subst n, rw [dif_pos rfl, dif_pos rfl, dif_pos rfl],
      simp only [preadditive.add_comp, preadditive.comp_add], },
    { rw [dif_neg hn, dif_neg hn, dif_neg hn, add_zero], },
  end }

-- move me
instance bounded_homotopy_category.single_additive (i : ℤ) :
  (bounded_homotopy_category.single C i).additive :=
{ map_add' := λ X Y f g, begin
    delta bounded_homotopy_category.single,
    dsimp,
    rw functor.map_add,
    refl
  end }

instance Ext.additive (i : ℤ) :
  (Ext i : (bounded_homotopy_category C)ᵒᵖ ⥤ bounded_homotopy_category C ⥤ Ab).additive :=
{ map_add' := λ X Y f g, begin
    ext B e,
    dsimp [Ext],
    rw [preadditive.comp_add, lift_add, preadditive.add_comp],
  end }

-- move me
instance Ext'.flip_additive (i : ℤ) (B : C) : ((Ext' i).flip.obj B).additive :=
{ map_add' := λ X Y f g,
  begin
    delta Ext',
    dsimp,
    rw [functor.map_add, op_add, functor.map_add],
    refl,
  end }

-- move me
instance Ext'.additive (i : ℤ) (A : Cᵒᵖ) : ((Ext' i).obj A).additive :=
{ map_add' := λ X Y f g,
  begin
    delta Ext',
    dsimp,
    rw [functor.map_add, functor.map_add],
  end }

end

-- move me
instance single_is_bounded_above (A : C) :
  is_bounded_above {as := (homological_complex.single C (complex_shape.up ℤ) 0).obj A} :=
begin
  refine ⟨⟨1, _⟩⟩,
  intros i hi,
  dsimp,
  rw if_neg,
  { exact is_zero_zero _ },
  { rintro rfl, exact zero_lt_one.not_le hi }
end

-- move me
instance quotient_single_is_bounded_above (A : C) :
  ((quotient C (complex_shape.up ℤ)).obj
    ((homological_complex.single C (complex_shape.up ℤ) 0).obj A)).is_bounded_above :=
single_is_bounded_above A

lemma is_zero_iff_epi_and_is_iso
  {A₁ A₂ A₃ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (B : C) (h : short_exact f g) :
  (∀ i > 0, is_zero (((Ext' i).obj (op A₃)).obj B)) ↔
  (epi (((Ext' 0).map f.op).app B) ∧ ∀ i > 0, is_iso (((Ext' i).map f.op).app B)) :=
begin
  let f' := (homological_complex.single _ (complex_shape.up ℤ) (0:ℤ)).map f,
  let g' := (homological_complex.single _ (complex_shape.up ℤ) (0:ℤ)).map g,
  let B' := (bounded_homotopy_category.single _ 0).obj B,
  have Hfg : ∀ (i : ℤ), short_exact (f'.f i) (g'.f i),
  { intro i, dsimp, by_cases hi : i = 0,
    { subst i, dsimp, simp only [eq_self_iff_true, category.comp_id, category.id_comp, if_true, h] },
    { rw [dif_neg hi, dif_neg hi, if_neg hi, if_neg hi, if_neg hi],
      refine ⟨exact_of_zero _ _⟩, } },
  split,
  { intro H,
    split,
    { have := ((Ext_five_term_exact_seq' f' g' 0 B' Hfg).drop 1).pair,
      refine this.epi_iff_eq_zero.mpr _,
      refine is_zero.eq_of_tgt _ _ _,
      exact H 1 zero_lt_one, },
    { rintro i (hi : 0 < i),
      apply (Ext_five_term_exact_seq' f' g' i B' Hfg).is_iso_of_zero_of_zero,
      { refine is_zero.eq_of_src _ _ _,
        exact H i hi, },
      { refine is_zero.eq_of_tgt _ _ _,
        exact H (i+1) (hi.trans $ lt_add_one _), }, } },
  { intros H i hi,
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i-1, sub_add_cancel _ _⟩,
    have := λ i, Ext_five_term_exact_seq' f' g' i B' Hfg,
    refine is_zero_of_exact_zero_zero' _ _ ((this i).drop 2).pair _ _,
    sorry { refine ((this i).drop 1).pair.epi_iff_eq_zero.mp _,
      rw [gt_iff_lt, int.lt_add_one_iff] at hi,
      obtain (rfl|hi) := hi.eq_or_lt,
      { exact H.1 },
      { show epi (((Ext i).map (of_hom f').op).app B'),
        -- this is sloooow...
        haveI : is_iso (((Ext i).map (of_hom f').op).app B') := H.2 i hi,
        exact regular_epi.epi (((Ext i).map (of_hom f').op).app B'), } },
    { refine (this (i+1)).pair.mono_iff_eq_zero.mp _,
      sorry
      -- timing out, for some reason
      -- show mono (((Ext (i+1)).map (of_hom f').op).app B'),
      -- haveI : is_iso (((Ext (i+1)).map (of_hom f').op).app B') := H.2 (i+1) hi,
      -- exact regular_mono.mono (((Ext i).map (of_hom f').op).app B'),
       } }
end

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
