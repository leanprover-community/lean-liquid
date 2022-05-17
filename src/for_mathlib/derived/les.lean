import for_mathlib.derived.derived_cat
import for_mathlib.derived.example

open category_theory category_theory.triangulated category_theory.limits

namespace bounded_derived_category

variables (A : Type*) [category A] [abelian A] [enough_projectives A]

instance Ext_additive_fst (i : ℤ) (X : bounded_derived_category A) :
  (((Ext A i).flip.obj X).right_op).additive :=
{ map_add' := begin
    intros Y Z f g, dsimp,
    conv_rhs { rw ← op_add }, congr' 1, ext e,
    dsimp, rw preadditive.add_comp,
  end }

instance Ext_homological_fst (i : ℤ) (X : bounded_derived_category A) :
  homological_functor ((Ext A i).flip.obj X).right_op :=
category_theory.triangulated.preadditive_yoneda_op_homological (X⟦i⟧)

end bounded_derived_category

namespace homological_complex

section

variables {A : Type*} [category A] [abelian A]
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

@[simps]
noncomputable def cone.π (w : ∀ i, f.f i ≫ g.f i = 0) :
  cone f ⟶ Z :=
{ f := λ i, biprod.snd ≫ g.f i,
  comm' := λ i j hij, begin
    dsimp at hij, subst j, dsimp [cone.d], rw [if_pos rfl, biprod.lift_snd_assoc],
    ext,
    { simp only [exact.w_assoc, zero_comp, category.assoc, biprod.inl_desc_assoc,
        category.id_comp, w, exact_inl_snd], },
    { simp only [category.assoc, biprod.inr_snd_assoc, biprod.inr_desc_assoc, g.comm], }
  end }

--generalize
@[simps]
noncomputable def kernel : cochain_complex A ℤ :=
{ X := λ i, kernel (f.f i),
  d := λ i j, kernel.map (f.f i) (f.f j) (X.d i j) (Y.d i j) (f.comm i j),
  shape' := λ i j hij, by { ext, simp only [kernel.lift_ι, zero_comp, X.shape i j hij, comp_zero] },
  d_comp_d' := λ i j k hij hjk, begin
    ext,
    simp only [category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, zero_comp, comp_zero, d_comp_d],
  end }

@[simps]
noncomputable def kernel.ι : kernel f ⟶ X :=
{ f := λ i, kernel.ι _,
  comm' := λ i j hij, by simp only [kernel_d, kernel.lift_ι] }

instance kernel.ι_mono (n : ℕ) : mono ((kernel.ι f).f n) :=
show mono (limits.kernel.ι (f.f n)), by apply_instance

end

variables {A : Type*} [category A] [abelian A] [enough_projectives A]
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

open_locale pseudoelement
open category_theory.abelian

-- move me
lemma biprod.lift_desc_comm {X₁ X₂ Y₁ Y₂ : A}
  (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
  biprod.lift (biprod.desc f₁₁ f₂₁) (biprod.desc f₁₂ f₂₂) =
  biprod.desc (biprod.lift f₁₁ f₁₂) (biprod.lift f₂₁ f₂₂) :=
by ext; simp only [category.assoc,
  biprod.lift_fst, biprod.lift_snd, biprod.inl_desc, biprod.inr_desc]

-- move me
lemma biprod.comp_lift {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (h : X ⟶ Z) :
  f ≫ biprod.lift g h = biprod.lift (f ≫ g) (f ≫ h) :=
by ext; simp only [category.assoc, biprod.lift_fst, biprod.lift_snd]

-- move me
lemma exact_of_exact_image {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (h : exact f (factor_thru_image g)) :
  exact f g :=
by { rw ← limits.image.fac g, exact exact_comp_mono h }

-- move me
@[reassoc]
lemma comp_factor_thru_image_eq_zero {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  f ≫ factor_thru_image g = 0 :=
by rw [← cancel_mono (limits.image.ι g), category.assoc, limits.image.fac, w, zero_comp]

open_locale zero_object

def cone.π_quasi_iso (w : ∀ i, short_exact (f.f i) (g.f i)) :
  quasi_iso (cone.π f g (λ i, (w i).exact.w)) :=
{ is_iso := λ i, begin
    have w'' : ∀ i, f.f i ≫ g.f i = 0 := λ i, (w i).exact.w,
    let π := cone.π f g w'',
    have aux : ∀ n, short_exact ((kernel.ι π).f n) (π.f n) := λ n,
    { mono := equalizer.ι_mono,
      epi := by { haveI := (w n).epi, exact category_theory.epi_comp _ _},
      exact := exact_kernel_ι },
    let K := kernel π,
    suffices : ∀ n, is_zero (homology K n),
    { exact (six_term_exact_seq (kernel.ι π) π aux i (i+1) rfl).is_iso_of_zero_of_zero
        ((this _).eq_of_src _ _) ((this _).eq_of_tgt _ _), },
    intro n,
    obtain ⟨n, rfl⟩ : ∃ k, k+1 = n := ⟨n-1, sub_add_cancel _ _⟩,
    refine is_zero_of_iso_of_zero _
      (homology_iso K n (n+1) (n+1+1) rfl rfl).symm,
    apply exact.homology_is_zero,
    apply pseudoelement.exact_of_pseudo_exact,
    split, { intro a, rw [← pseudoelement.comp_apply, d_comp_d, pseudoelement.zero_apply], },
    intros b hb,
    set x := (kernel.ι π).f (n+1) b with xdef,
    have hx : π.f _ x = 0,
    { dsimp only [x, kernel.ι_f],
      rw [← pseudoelement.comp_apply, exact_kernel_ι.w, pseudoelement.zero_apply],
      apply_instance },
    let y := (biprod.snd : (X.X _) ⊞ (Y.X (n+1)) ⟶ Y.X (n+1)) x,
    have hy : g.f _ y = 0,
    { dsimp only [y], rw [← pseudoelement.comp_apply], exact hx },
    have w' := @pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ (w (n+1)).exact,
    obtain ⟨a, ha⟩ := w'.2 y hy,
    let a' : ↥((X.X (n+1)) ⊞ (Y.X n)) := (biprod.inl : _ ⟶ (X.X (n+1)) ⊞ (Y.X n)) a,
    have ha' : π.f n a' = 0,
    { dsimp only [a', π, cone.π_f],
      rw [← pseudoelement.comp_apply, (exact_inl_snd (X.X (n+1)) _).w_assoc,
        zero_comp, pseudoelement.zero_apply], },
    have aux' := @pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ (aux n).exact,
    obtain ⟨a'', ha''⟩ := aux'.2 a' ha',
    refine ⟨a'', _⟩,
    apply @pseudoelement.pseudo_injective_of_mono _ _ _ _ _ _ (aux (n+1)).mono,
    rw [← pseudoelement.comp_apply, ← (kernel.ι π).comm, pseudoelement.comp_apply, ha''],
    let φ : (cone f).X (n+1) ⟶ Y.X (n+1+1) ⊞ Y.X (n+1) :=
    biprod.lift (biprod.fst ≫ f.f _) biprod.snd,
    have hφ : mono φ,
    { haveI : mono (f.f (n+1+1)) := (w _).mono,
      constructor, intros Z α β H, dsimp [φ] at H,
      apply category_theory.limits.biprod.hom_ext,
      { rw ← cancel_mono (f.f (n+1+1)), apply_fun (λ ψ, ψ ≫ biprod.fst) at H,
        simpa only [category.assoc, biprod.lift_fst] using H, },
      { apply_fun (λ ψ, ψ ≫ biprod.snd) at H,
        simpa only [category.assoc, biprod.lift_snd] using H, } },
    apply_fun ⇑((kernel.ι π).f (n+1+1)) at hb,
    rw [← pseudoelement.comp_apply, ← (kernel.ι π).comm, pseudoelement.comp_apply,
      pseudoelement.apply_zero, ← xdef] at hb,
    dsimp only [cone_d, cone.d] at hb ⊢, rw [dif_pos rfl] at hb ⊢,
    change _ = x,
    simp only [X_eq_to_iso_refl, category.comp_id] at hb ⊢,
    simp only [← pseudoelement.comp_apply, category.assoc],
    simp only [biprod.lift_desc_comm, biprod.inl_desc] at hb ⊢,
    apply @pseudoelement.pseudo_injective_of_mono _ _ _ _ _ _ hφ,
    rw [← pseudoelement.comp_apply, biprod.comp_lift, biprod.lift_fst_assoc, biprod.lift_snd,
      ← category.comp_id (f.f (n+1)), preadditive.neg_comp, ← f.comm, ← preadditive.comp_neg,
      ← biprod.comp_lift, pseudoelement.comp_apply, ha, ← pseudoelement.comp_apply,
      biprod.comp_lift, category.comp_id],
    -- use `hb`
    sorry
  end }

end homological_complex

/-
    have w' : ∀ i, f.f i ≫ g.f i = 0 := λ i, (w i).exact.w,
    let π := cone.π f g w',
    have aux : ∀ n, short_exact ((kernel.ι π).f n) (π.f n) := λ n,
    { mono := equalizer.ι_mono,
      epi := by { haveI := (w n).epi, exact category_theory.epi_comp _ _},
      exact := exact_kernel_ι },
    let K := kernel π,
    suffices : ∀ n, is_zero (homology K n),
    { exact (six_term_exact_seq (kernel.ι π) π aux i (i+1) rfl).is_iso_of_zero_of_zero
        ((this _).eq_of_src _ _) ((this _).eq_of_tgt _ _), },
    intro n,
    obtain ⟨n, rfl⟩ : ∃ k, k+1 = n := ⟨n-1, sub_add_cancel _ _⟩,
    refine is_zero_of_iso_of_zero _
      (homology_iso K n (n+1) (n+1+1) rfl rfl).symm,
    apply exact.homology_is_zero,
    apply exact_of_exact_image,
    let Kd := K.d (n+1) (n+1+1),
    let Cd := (cone f).d (n+1) (n+1+1),
    let v2 := (kernel.ι π).f (n+1),
    let sq : arrow.mk (Kd) ⟶ arrow.mk Cd :=
    ⟨(kernel.ι π).f _, (kernel.ι π).f _, _⟩, swap,
    { dsimp [Kd, Cd], simp only [kernel.lift_ι], },
    let v3 : image Kd ⟶ image Cd := image.map sq,
    have sq2 : factor_thru_image Kd ≫ v3 = v2 ≫ factor_thru_image Cd,
    { apply image.factor_map sq },
    let q : cokernel v2 ⟶ cokernel v3 :=
      cokernel.map _ _ (factor_thru_image Kd) (factor_thru_image Cd) sq2.symm,
    have sq4 : factor_thru_image Cd ≫ cokernel.π v3 = cokernel.π v2 ≫ q,
    { symmetry, apply cokernel.π_desc, },
    let φ : (cone f).X n ⟶ (limits.kernel q) :=
      kernel.lift _ ((cone f).d n (n+1) ≫ cokernel.π v2) _, swap,
    { rw [category.assoc, ← sq4, comp_factor_thru_image_eq_zero_assoc, zero_comp],
      exact d_comp_d _ _ _ _ },
    suffices S : category_theory.snake
      (K.X n)          (K.X (n+1))          (image Kd)
      ((cone f).X n)   ((cone f).X (n+1))   (image Cd)
      _                (cokernel v2)        (cokernel v3)
      _                0                    0
      (K.d n (n+1))          (factor_thru_image Kd)
      ((kernel.ι π).f n)     ((kernel.ι π).f (n+1))     v3
      ((cone f).d n (n+1))   (factor_thru_image Cd)
      φ                      (cokernel.π v2)            (cokernel.π v3)
      (limits.kernel.ι q)     q
      (cokernel.π φ)    0    0
      0  0,
    { exact S.six_term_exact_seq.pair },
    apply_with snake.mk {instances := ff};
    try { apply_instance },
    { sorry },
    { exact exact_kernel_ι },
-/
