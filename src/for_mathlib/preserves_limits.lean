import for_mathlib.homological_complex_abelian
import category_theory.limits.preserves.finite
import category_theory.limits.preserves.shapes.kernels
import for_mathlib.homology

.

open category_theory category_theory.limits

universes v u₁ u₂

variables {C : Type u₁} [category.{v} C] [abelian C]
variables {D : Type u₂} [category.{v} D] [abelian D] (F : C ⥤ D)
variables [preserves_finite_limits F] [preserves_finite_colimits F] [functor.additive F]
variables {ι : Type*} {c : complex_shape ι}

@[simps] noncomputable
def category_theory.limits.cokernel.map_arrow_iso {C : Type u₁} [category.{v} C]
  [has_zero_morphisms C] {X₁ Y₁ X₂ Y₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [has_cokernel f₁] [has_cokernel f₂]
  (e : arrow.mk f₁ ≅ arrow.mk f₂) : cokernel f₁ ≅ cokernel f₂ :=
{ hom := cokernel.map _ _ e.hom.left e.hom.right e.hom.w.symm,
  inv := cokernel.map _ _ e.inv.left e.inv.right e.inv.w.symm,
  hom_inv_id' := begin
    ext,
    simp only [category.comp_id, cokernel.π_desc, cokernel.π_desc_assoc,
      category.assoc, coequalizer_as_cokernel],
    rw [← category.assoc, ← comma.comp_right, e.hom_inv_id, arrow.id_right],
    exact category.id_comp _
  end,
  inv_hom_id' := begin
    ext,
    simp only [category.comp_id, cokernel.π_desc, cokernel.π_desc_assoc,
      category.assoc, coequalizer_as_cokernel],
    rw [← category.assoc, ← comma.comp_right, e.inv_hom_id, arrow.id_right],
    exact category.id_comp _
  end }

@[simps] noncomputable
def category_theory.limits.kernel.map_arrow_iso {C : Type u₁} [category.{v} C]
  [has_zero_morphisms C] {X₁ Y₁ X₂ Y₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [has_kernel f₁] [has_kernel f₂]
  (e : arrow.mk f₁ ≅ arrow.mk f₂) : kernel f₁ ≅ kernel f₂ :=
{ hom := kernel.map _ _ e.hom.left e.hom.right e.hom.w.symm,
  inv := kernel.map _ _ e.inv.left e.inv.right e.inv.w.symm,
  hom_inv_id' := begin
    ext,
    simp only [category.id_comp, kernel.lift_ι, kernel.lift_ι_assoc,
      category.assoc, equalizer_as_kernel],
    rw [← comma.comp_left, e.hom_inv_id, arrow.id_left],
    exact category.comp_id _
  end,
  inv_hom_id' := begin
    ext,
    simp only [category.id_comp, kernel.lift_ι, kernel.lift_ι_assoc,
      category.assoc, equalizer_as_kernel],
    rw [← comma.comp_left, e.inv_hom_id, arrow.id_left],
    exact category.comp_id _
  end }

noncomputable
def category_theory.functor.map_homological_complex_X_prev (F : C ⥤ D) [F.additive]
  (X : homological_complex C c) (i : ι) :
  ((F.map_homological_complex c).obj X).X_prev i ≅ F.obj (X.X_prev i) :=
iso.refl _

lemma category_theory.functor.map_homological_complex_X_prev_eq (F : C ⥤ D) [F.additive]
  (X : homological_complex C c) {i j : ι} :
  F.map_homological_complex_X_prev X i = iso.refl _ := rfl

noncomputable
def category_theory.functor.map_homological_complex_X_next (F : C ⥤ D) [F.additive]
  (X : homological_complex C c) (i : ι) :
  ((F.map_homological_complex c).obj X).X_next i ≅ F.obj (X.X_next i) :=
iso.refl _

lemma category_theory.functor.map_homological_complex_X_next_eq (F : C ⥤ D) [F.additive]
  (X : homological_complex C c) {i j : ι} :
  F.map_homological_complex_X_next X i = iso.refl _ := rfl

lemma category_theory.functor.map_homological_complex_d_from (F : C ⥤ D) [F.additive]
  (X : homological_complex C c) (i : ι) :
  ((F.map_homological_complex c).obj X).d_from i = F.map (X.d_from i) := rfl

lemma category_theory.functor.map_homological_complex_d_to (F : C ⥤ D) [F.additive]
  (X : homological_complex C c) (i : ι) :
  ((F.map_homological_complex c).obj X).d_to i = F.map (X.d_to i) := rfl

@[simp, reassoc]
lemma category_theory.limits.preserves_kernel_iso_inv_map (F : C ⥤ D)
  [F.additive] [preserves_finite_limits F]
  {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (iX : X₁ ⟶ X₂) (iY : Y₁ ⟶ Y₂) (e) :
  (preserves_kernel.iso F f₁).inv ≫ F.map (kernel.map _ _ iX iY e) =
    kernel.map _ _ (F.map iX) (F.map iY) (by simp_rw [← F.map_comp, e]) ≫
      (preserves_kernel.iso F f₂).inv :=
begin
  rw [iso.eq_comp_inv, category.assoc, eq_comm, iso.eq_inv_comp],
  ext,
  simp,
end
-- attribute [reassoc] kernel.lift_map

open category_theory category_theory.limits

@[simp, reassoc]
lemma homology.π'_iso_cokernel_lift_hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  homology.π' f g w ≫ (homology_iso_cokernel_lift f g w).hom = cokernel.π _ :=
begin
  delta homology.π', simp,
end

@[reassoc]
lemma homology.π'_iso_cokernel_lift_inv {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  cokernel.π _ ≫ (homology_iso_cokernel_lift f g w).inv = homology.π' f g w := rfl

noncomputable
def preserves_homology_of_exact (i : ι) :
  F.map_homological_complex c ⋙ homology_functor _ c i ≅ homology_functor _ c i ⋙ F :=
begin
  fapply nat_iso.of_components,
  { intro X,
    refine homology_iso_cokernel_lift _ _ _ ≪≫
      cokernel.map_arrow_iso _ _ (arrow.iso_mk _ _ _) ≪≫
      (preserves_cokernel.iso _ _).symm ≪≫ F.map_iso (homology_iso_cokernel_lift _ _ _).symm,
    { exact iso.refl _ },
    { refine kernel.map_arrow_iso _ _ (arrow.iso_mk _ _ _) ≪≫ (preserves_kernel.iso _ _).symm,
      { exact iso.refl _ },
      { exact iso.refl _ },
      { dsimp, rw [category.id_comp, F.map_homological_complex_d_from, category.comp_id] } },
    { dsimp, rw [← category.assoc, iso.eq_comp_inv], ext, simp [F.map_homological_complex_d_to] } },
  { intros X Y f, apply homology.hom_from_ext,
    simp only [category_theory.limits.kernel.map_arrow_iso_hom,
      category_theory.functor.map_iso_inv,
      category_theory.functor.map_homological_complex_map_f,
      homological_complex.hom.sq_from_right,
      category_theory.iso.refl_hom,
      homology.π'_iso_cokernel_lift_hom_assoc,
      category_theory.arrow.iso_mk_hom_right,
      category_theory.arrow.iso_mk_hom_left,
      category_theory.limits.cokernel.map_arrow_iso_hom,
      category_theory.functor.comp_map,
      homology_functor_map,
      category_theory.iso.symm_hom,
      category_theory.limits.cokernel.π_desc_assoc,
      category_theory.limits.preserves_cokernel.iso_inv,
      category_theory.functor.map_iso_symm,
      category_theory.category.assoc,
      category_theory.iso.trans_hom,
      homological_complex.hom.sq_to_right,
      category_theory.limits.π_comp_cokernel_comparison_assoc,
      homology.π'_map_assoc],
    simp only [← functor.map_comp],
    rw [homology.π'_iso_cokernel_lift_inv_assoc, homology.π'_iso_cokernel_lift_inv, homology.π'_map,
      F.map_comp, preserves_kernel_iso_inv_map_assoc],
    simp only [← category.assoc],
    congr' 2,
    ext,
    simp only [category_theory.limits.equalizer_as_kernel,
      homological_complex.hom.sq_from_right,
      category_theory.category.assoc,
      category_theory.limits.kernel.lift_ι,
      homological_complex.hom.sq_to_right,
      category_theory.limits.kernel.lift_ι_assoc],
    dsimp,
    rw [category.id_comp, category.comp_id] }
end
.

-- def preserves_limit_of_lim_commute (J : Type*) [category J] [has_limits_of_shape J C]
--   [has_limits_of_shape J D]  (F : C ⥤ D) (e : lim ⋙ F ≅ (whiskering_right J C D).obj F ⋙ lim):
--     preserves_limits_of_shape J F :=
-- begin
--   refine ⟨λ K, preserves_limit_of_preserves_limit_cone (limit.is_limit _) _⟩,
--   apply is_limit.of_iso_limit (limit.is_limit _),
--   ext, swap,
--   { exact e.symm.app K },
--   { dsimp,
--     have := congr_arg (λ f, f ≫ limit.π _ j) (e.hom.naturality (limit.cone K).π),
--     dsimp at this,
--     simp only [whisker_right_app, limit.cone_π, lim_map_π, category.assoc] at this,
--     let : limit K ≅ limit ((category_theory.functor.const J).obj (limit K)),
--     { refine ⟨limit.lift _ ⟨_, 𝟙 _⟩, lim_map (limit.cone K).π, _, _⟩,
--       { ext, simp },
--       { ext, simp, dsimp, simp,  } }  }
--   -- have := cone.iso_mk
-- end
