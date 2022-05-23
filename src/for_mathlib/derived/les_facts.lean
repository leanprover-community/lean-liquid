import for_mathlib.derived.example
import for_mathlib.derived.les3

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

lemma is_zero_iff_epi_and_is_iso
  {A₁ A₂ A₃ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (B : C) (h : short_exact f g) :
  (∀ i > 0, is_zero (((Ext' i).obj (op A₃)).obj B)) ↔
  (epi (((Ext' 0).map f.op).app B) ∧ ∀ i > 0, is_iso (((Ext' i).map f.op).app B)) :=
begin
  have LES := λ i, h.Ext'_five_term_exact_seq B i,
  split,
  { intro H,
    split,
    { have := ((LES 0).drop 1).pair,
      refine this.epi_iff_eq_zero.mpr _,
      refine is_zero.eq_of_tgt _ _ _,
      exact H 1 zero_lt_one, },
    { rintro i (hi : 0 < i),
      apply (LES i).is_iso_of_zero_of_zero,
      { refine is_zero.eq_of_src _ _ _,
        exact H i hi, },
      { refine is_zero.eq_of_tgt _ _ _,
        exact H (i+1) (hi.trans $ lt_add_one _), }, } },
  { intros H i hi,
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i-1, sub_add_cancel _ _⟩,
    refine is_zero_of_exact_zero_zero' _ _ ((LES i).drop 2).pair _ _,
    { refine ((LES i).drop 1).pair.epi_iff_eq_zero.mp _,
      rw [gt_iff_lt, int.lt_add_one_iff] at hi,
      obtain (rfl|hi) := hi.eq_or_lt,
      { exact H.1 },
      { exact @is_iso.epi_of_iso _ _ _ _ _ (H.2 _ hi), } },
    { refine (LES (i+1)).pair.mono_iff_eq_zero.mp _,
      exact @is_iso.mono_of_iso _ _ _ _ _ (H.2 _ hi), } }
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
begin
  let E : ℤ → Cᵒᵖ ⥤ Ab := λ n, (Ext' n).flip.obj Z,
  have H1 := λ i, hf.Ext'_five_term_exact_seq Z i,
  have H2 := λ i, hg.Ext'_five_term_exact_seq Z i,
  have sq1 : ∀ i, (E i).map α₃.op ≫ (E i).map f₂.op = (E i).map g₂.op ≫ (E i).map α₂.op,
  { intro, simp only [← (E i).map_comp, ← op_comp, sq₂], },
  have sq2 : ∀ i, (E i).map α₂.op ≫ (E i).map f₁.op = (E i).map g₁.op ≫ (E i).map α₁.op,
  { intro, simp only [← (E i).map_comp, ← op_comp, sq₁], },
  have sq3 : ∀ i, (E i).map α₁.op ≫ Ext'_δ Z hf i = Ext'_δ Z hg i ≫ (E (i+1)).map α₃.op,
  { apply Ext'_δ_natural f₁ f₂ g₁ g₂ α₁ α₂ α₃ sq₁ sq₂ Z hf hg, },
  split; rintro ⟨h1, h2⟩,
  { split,
    { show epi (((E 0).map α₂.op)),
      refine abelian.epi_of_epi_of_epi_of_mono (sq1 0) (sq2 0) (sq3 0)
        ((H2 0).drop 1).pair ((H1 0).drop 0).pair ((H1 0).drop 1).pair _ h1 _,
      { exact @is_iso.epi_of_iso _ _ _ _ _ (H 0), },
      { exact @is_iso.mono_of_iso _ _ _ _ _ (H 1), } },
    { rintros i (hi : 0 < i),
      suffices : mono ((E i).map α₂.op) ∧ epi ((E i).map α₂.op),
      { cases this with aux1 aux2, refine @is_iso_of_mono_of_epi _ _ _ _ _ _ aux1 aux2 },
      split,
      { obtain ⟨i, rfl⟩ : ∃ j, j+1 = i := ⟨i-1, sub_add_cancel _ _⟩,
        refine abelian.mono_of_epi_of_mono_of_mono (sq3 i) (sq1 (i+1)) (sq2 (i+1))
          ((H2 i).drop 2).pair ((H2 (i+1)).drop 0).pair ((H1 i).drop 2).pair _ _ _,
        { obtain (rfl|hi') := eq_or_ne i 0,
          { apply h1 },
          { refine @is_iso.epi_of_iso _ _ _ _ _ (h2 _ _),
            rw int.lt_add_one_iff at hi, refine lt_of_le_of_ne hi hi'.symm, } },
        { exact @is_iso.mono_of_iso _ _ _ _ _ (H _), },
        { exact @is_iso.mono_of_iso _ _ _ _ _ (h2 _ hi), } },
      { refine abelian.epi_of_epi_of_epi_of_mono (sq1 i) (sq2 i) (sq3 i)
          ((H2 i).drop 1).pair ((H1 i).drop 0).pair ((H1 i).drop 1).pair _ _ _,
        { exact @is_iso.epi_of_iso _ _ _ _ _ (H _), },
        { exact @is_iso.epi_of_iso _ _ _ _ _ (h2 _ hi), },
        { exact @is_iso.mono_of_iso _ _ _ _ _ (H _), } } } },
  { split,
    { refine abelian.epi_of_epi_of_epi_of_mono (sq2 0) (sq3 0) (sq1 1)
        ((H2 0).drop 2).pair ((H1 0).drop 1).pair ((H1 0).drop 2).pair h1 _ _,
      { exact @is_iso.epi_of_iso _ _ _ _ _ (H 1), },
      { exact @is_iso.mono_of_iso _ _ _ _ _ (h2 _ zero_lt_one), } },
    { intros i hi,
      refine abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso'
        (sq1 i) (sq2 i) (sq3 i) (sq1 (i+1))
        (H2 i).pair ((H2 i).drop 1).pair ((H2 i).drop 2).pair
        (H1 i).pair ((H1 i).drop 1).pair ((H1 i).drop 2).pair
        (H _) (h2 _ hi) (H _) (h2 _ (add_pos hi zero_lt_one)), } }
end
