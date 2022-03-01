import category_theory.functor.category

import for_mathlib.homology
import for_mathlib.derived_functor


universes w v u

noncomputable theory

namespace category_theory

open functor functor.left_derived

variables {C : Type u} {D : Type v} [category.{w} C] [category.{w} D]
variables (F : C ⥤ D) {A₁ A₂ A₃ X : C} {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃}
variables [abelian C] [abelian D] [additive F]

namespace limits

/-- The iso `parallel_pair f 0 ⋙ F ≅ parallel_pair (F.map f) 0`. -/
def cokernel_diagram_iso {A B : C} (f : A ⟶ B) :
  parallel_pair f 0 ⋙ F ≅ parallel_pair (F.map f) 0 :=
nat_iso.of_components (λ X,
  match X with
  | walking_parallel_pair.zero := iso.refl _
  | walking_parallel_pair.one := iso.refl _
  end)
begin
  rintros (a|a) (b|b) (f|f),
  work_on_goal 0 { dsimp at *, simp at *, dsimp at *, simp at * },
  work_on_goal 0 { dsimp at *, unfold_aux, dsimp at *, simp at * },
  work_on_goal 0 { dsimp at *, simp at * },
  dsimp at *, simp at *, dsimp at *, simp at *,
end

/-- A morphism `cokernel f ⟶ A₃` provided that `f ≫ g = 0`. -/
def cokernel_comparison (w : f ≫ g = 0) : cokernel f ⟶ A₃ :=
cokernel.desc f g w

end limits

namespace functor.right_exact

open limits

/-- The iso `F.obj (cokernel f) ≅ cokernel (F.map f)` if `preserves_finite_colimits F`. -/
def preserves_cokernel [preserves_finite_colimits F] {A B : C} (f : A ⟶ B) :
  F.obj (cokernel f) ≅ cokernel (F.map f) :=
(is_colimit_of_preserves _ (colimit.is_colimit _)).cocone_point_unique_up_to_iso
  (colimit.is_colimit _) ≪≫ limits.has_colimit.iso_of_nat_iso
  (cokernel_diagram_iso _ _)

@[simp, reassoc]
lemma map_preserves_cokernel_hom [limits.preserves_finite_colimits F] :
  F.map (cokernel.π f) ≫ (preserves_cokernel F f).hom = cokernel.π (F.map f) :=
begin
  erw (is_colimit_of_preserves F (colimit.is_colimit (parallel_pair f 0))).fac_assoc,
  dsimp, simp only [has_colimit.iso_of_nat_iso_ι_hom],
  dsimp [cokernel_diagram_iso],
  simp,
end

variable {F}

-- Do we have some API with `exact_seq` to get lemmas like this?
lemma comp_eq_zero (ex : exact_seq C [f, g, (0 : A₃ ⟶ X)]) : f ≫ g = 0 :=
begin
  suffices : exact f g, by exact this.1,
  rw exact_iff_exact_seq,
  exact ex.extract 0 2,
end

variable (F)

lemma map_comp_eq_zero (ex : exact_seq C [f, g, (0 : A₃ ⟶ X)]) : F.map f ≫ F.map g = 0 :=
by { rw [← F.map_comp, comp_eq_zero ex], simp }

variable {F}

local attribute [instance] abelian.pseudoelement.over_to_sort
  abelian.pseudoelement.hom_to_fun
  abelian.pseudoelement.has_zero

instance comparison_is_iso_of_exact (ex : exact_seq C [f, g, (0 : A₃ ⟶ X)]) :
  is_iso (cokernel_comparison (comp_eq_zero ex)) :=
begin
  letI : epi g := ((abelian.tfae_epi X g).out 0 2).2 ((exact_iff_exact_seq _ _).2 $ ex.extract 1 2),
  refine (is_iso_iff_mono_and_epi _).2 ⟨_, limits.cokernel.desc_epi _ _ _⟩,
  refine abelian.pseudoelement.mono_of_zero_of_map_zero _ (λ a ha, _),
  obtain ⟨b, hb⟩ := abelian.pseudoelement.pseudo_surjective_of_epi (cokernel.π f) a,
  have hbz : g b = 0,
  { have : g = (cokernel.π f) ≫ (cokernel_comparison (comp_eq_zero ex)) :=
      (cokernel.π_desc _ _ _).symm,
    rw [this, abelian.pseudoelement.comp_apply, hb, ha] },
  obtain ⟨c, hc : f c = b⟩ := abelian.pseudoelement.pseudo_exact_of_exact.2 _ hbz,
  { rw [← hc, ← abelian.pseudoelement.comp_apply, cokernel.condition,
      abelian.pseudoelement.zero_apply] at hb,
    exact hb.symm },
  { exact (exact_iff_exact_seq _ _).2 (ex.extract 0 2) }
end

@[simp, reassoc]
lemma cokernel_comparison_inv (ex : exact_seq C [f, g, (0 : A₃ ⟶ X)]) :
  g ≫ inv (cokernel_comparison (comp_eq_zero ex)) = cokernel.π _ :=
begin
  rw is_iso.comp_inv_eq,
  dsimp [cokernel_comparison],
  simp,
end

lemma aux [limits.preserves_finite_colimits F] (ex : exact_seq C [f, g, (0 : A₃ ⟶ X)]) :
  F.map g ≫ (F.map $ inv (cokernel_comparison (comp_eq_zero ex))) ≫ (preserves_cokernel _ _).hom =
  cokernel.π (F.map f) :=
by simp only [← category.assoc, ← F.map_comp, cokernel_comparison_inv, map_preserves_cokernel_hom]

variable (F)

lemma preserves_exact_seq [limits.preserves_finite_colimits F]
  (ex : exact_seq C [f, g, (0 : A₃ ⟶ X)]) :
  exact_seq D [F.map f, F.map g, (0 : F.obj A₃ ⟶ F.obj X)] :=
begin
  have exact := (exact_iff_exact_seq _ _).2 (ex.extract 0 2),
  haveI epi : epi g,
  { replace ex : exact_seq C ([g, _]) := ex.extract 1 2,
    rwa [← exact_iff_exact_seq, ← (abelian.tfae_epi X g).out 0 2] at ex },
  refine exact_seq.cons _ _ _ _ _,
  { let I : F.obj A₃ ≅ cokernel (F.map f) :=
      (F.map_iso $ (as_iso $ cokernel_comparison (comp_eq_zero ex)).symm) ≪≫ preserves_cokernel _ _,
    suffices : category_theory.exact (F.map f) (F.map g ≫ I.hom), by rwa exact_comp_iso at this,
    erw aux,
    exact abelian.exact_cokernel (F.map f) },
  rw [← exact_iff_exact_seq, ← (abelian.tfae_epi (F.obj X) (F.map g)).out 0 2],
  exact category_theory.preserves_epi _ _,
end

lemma short_exact_of_resolution (P: ProjectiveResolution X) : exact_seq C
  [P.complex.d 1 0, P.π.f 0, (0 : X ⟶ X)] :=
begin
  refine exact_seq.cons _ _ P.exact₀ _ _,
  rw ← exact_iff_exact_seq,
  exact ((abelian.tfae_epi X (P.π.f 0)).out 0 2).1 P.epi
end

lemma short_exact_of_resolution_functor (P: ProjectiveResolution X)
  [limits.preserves_finite_colimits F] : exact_seq D
  [((F.map_homological_complex (complex_shape.down ℕ)).obj P.complex).d_to 0,
  F.map (P.π.f 0), (0 : F.obj X ⟶ F.obj X)] :=
begin
  refine exact_seq.cons _ _ _ _ _,
  { have : (complex_shape.down ℕ).rel 1 0 := rfl,
    let f := (homological_complex.X_prev_iso ((F.map_homological_complex _).obj P.complex) this),
    refine preadditive.exact_of_iso_of_exact' (F.map (P.complex.d 1 0)) (F.map (P.π.f 0)) _ _
      f.symm (iso.refl _) (iso.refl _) (by simp) (by simp) _,
    exact (exact_iff_exact_seq _ _ ).2
      ((preserves_exact_seq F (short_exact_of_resolution P)).extract 0 2) },
  rw ← exact_iff_exact_seq,
  refine ((abelian.tfae_epi (F.obj X) (F.map (P.π.f 0))).out 0 2).1
    (category_theory.preserves_epi F _),
end

/-- Given `P : ProjectiveResolution X`, a morphism `(F.left_derived 0).obj X ⟶ F.obj X`. -/
@[nolint unused_arguments]
def left_derived.zero_to_self_app [enough_projectives C] {X : C}
  (P : ProjectiveResolution X) : (F.left_derived 0).obj X ⟶ F.obj X :=
(left_derived_obj_iso F 0 P).hom ≫ homology.desc' _ _ _ (kernel.ι _ ≫ (F.map (P.π.f 0)))
begin
  { have : (complex_shape.down ℕ).rel 1 0 := rfl,
    rw [kernel.lift_ι_assoc, homological_complex.d_to_eq _ this, map_homological_complex_obj_d,
      category.assoc, ← functor.map_comp],
    simp },
end
≫ F.map (𝟙 _)

/-- Given `P : ProjectiveResolution X`, a morphism `F.obj X ⟶ (F.left_derived 0).obj X` given
`preserves_finite_colimits F`. -/
@[nolint unused_arguments]
def left_derived.zero_to_self_app_inv [enough_projectives C] [preserves_finite_colimits F] {X : C}
  (P : ProjectiveResolution X) : F.obj X ⟶ (F.left_derived 0).obj X :=
begin
  refine ((@as_iso _ _ _ _ _ (category_theory.functor.right_exact.comparison_is_iso_of_exact
    (short_exact_of_resolution_functor F P))).inv) ≫ _ ≫ (homology_iso_cokernel_lift _ _ _).inv ≫
    (left_derived_obj_iso F 0 P).inv,
  exact cokernel.map _ _ (𝟙 _) (kernel.lift _ (𝟙 _) (by simp)) (by { ext, simp }),
end

lemma left_derived.zero_to_self_app_comp_inv [enough_projectives C] [preserves_finite_colimits F]
  {X : C} (P : ProjectiveResolution X) : left_derived.zero_to_self_app F P ≫
  left_derived.zero_to_self_app_inv F P = 𝟙 _ :=
begin
  dsimp [left_derived.zero_to_self_app, left_derived.zero_to_self_app_inv],
  rw [functor.map_id, category.comp_id, category.assoc],
  refine (iso.eq_inv_comp _).1 _,
  rw [← category.assoc, ← category.assoc, ← category.assoc],
  refine (iso.comp_inv_eq _).2 _,
  rw [category.comp_id, iso.inv_hom_id, iso.comp_inv_eq, category.id_comp],
  ext,
  simp only [category.assoc, homology.desc'_π'_assoc, cokernel_comparison_inv_assoc,
    cokernel.π_desc, homology.π', iso.inv_hom_id, category.comp_id],
  nth_rewrite 1 [← category.comp_id (cokernel.π _)],
  refine congr_arg (category_struct.comp _) _,
  dsimp [homology.desc'],
  rw [← category.assoc, ← category.assoc, ← category.assoc, iso.inv_hom_id, category.id_comp],
  ext,
  simp only [coequalizer_as_cokernel, category.assoc, cokernel.π_desc_assoc,
    cokernel_comparison_inv_assoc, cokernel.π_desc, category.comp_id],
  rw [← category.assoc],
  nth_rewrite 1 [← category.id_comp (cokernel.π _)],
  refine congr_fun (congr_arg category_struct.comp _) _,
  ext,
  simp only [category.assoc, kernel.lift_ι, category.comp_id, category.id_comp],
end

lemma left_derived.zero_to_self_app_inv_comp [enough_projectives C] [preserves_finite_colimits F]
  {X : C} (P : ProjectiveResolution X) : left_derived.zero_to_self_app_inv F P ≫
  left_derived.zero_to_self_app F P = 𝟙 _ :=
begin
  dsimp [left_derived.zero_to_self_app, left_derived.zero_to_self_app_inv],
  rw [functor.map_id, category.comp_id, category.assoc, category.assoc, category.assoc,
    ← category.assoc (F.left_derived_obj_iso 0 P).inv, iso.inv_hom_id, category.id_comp,
    is_iso.inv_comp_eq, category.comp_id],
  ext,
  simp only [cokernel.π_desc_assoc, category.assoc, cokernel.π_desc, homology.desc',
    cokernel_comparison],
  rw [← category.assoc, ← category.assoc (homology_iso_cokernel_lift _ _ _).inv, iso.inv_hom_id,
    category.id_comp],
  simp only [category.assoc, cokernel.π_desc, kernel.lift_ι_assoc, category.id_comp],
end

/-- Given `P : ProjectiveResolution X`, the isomorphism `(F.left_derived 0).obj X ≅ F.obj X` if
`preserves_finite_colimits F`. -/
def left_derived.zero_to_self_app_iso [enough_projectives C] [preserves_finite_colimits F]
  {X : C} (P : ProjectiveResolution X) : (F.left_derived 0).obj X ≅ F.obj X :=
{ hom := left_derived.zero_to_self_app _ P,
  inv := left_derived.zero_to_self_app_inv _ P,
  hom_inv_id' := left_derived.zero_to_self_app_comp_inv _ P,
  inv_hom_id' := left_derived.zero_to_self_app_inv_comp _ P }

/-- Given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y` and a morphism `f : X ⟶ Y`,
naturality of the square given by `left_derived.zero_to_self_obj_hom. -/
lemma left_derived.zero_to_self_natural [enough_projectives C] {X : C} {Y : C} (f : X ⟶ Y)
  (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
  (F.left_derived 0).map f ≫ left_derived.zero_to_self_app F Q =
  left_derived.zero_to_self_app F P ≫ F.map f :=
begin
  dsimp only [left_derived.zero_to_self_app],
  let f₁ := ProjectiveResolution.lift f P Q,
  rw [functor.left_derived_map_eq F 0 f f₁ (by simp),
    category.assoc, category.assoc, ← category.assoc _ (F.left_derived_obj_iso 0 Q).hom,
    iso.inv_hom_id, category.id_comp, category.assoc, category.assoc],
  congr' 1,
  rw [functor.map_id, functor.map_id, category.id_comp, category.comp_id],
  dsimp only [homology_functor_map],
  ext,
  simp only [homological_complex.hom.sq_to_right, map_homological_complex_map_f,
    homology.π'_map_assoc, homology.desc'_π', kernel.lift_ι_assoc, category.assoc,
    homology.desc'_π'_assoc],
  rw [← functor.map_comp, ← functor.map_comp],
  congr' 2,
  exact homological_complex.congr_hom (ProjectiveResolution.lift_commutes f P Q) 0
end

/-- The natural transformation `nat_trans (F.left_derived 0) F`. -/
def left_derived.zero_to_self [enough_projectives C] : (F.left_derived 0) ⟶ F :=
{ app := λ X, left_derived.zero_to_self_app F (ProjectiveResolution.of X),
  naturality' := λ X Y f, left_derived.zero_to_self_natural F f (ProjectiveResolution.of X)
    (ProjectiveResolution.of Y) }

/-- Given `preserves_finite_colimits F`, the natural isomorphism `(F.left_derived 0) ≅ F`. -/
def left_derived.zero_iso_self [enough_projectives C] [preserves_finite_colimits F] :
  (F.left_derived 0) ≅ F :=
nat_iso.of_components (λ X, left_derived.zero_to_self_app_iso _ (ProjectiveResolution.of X))
  (λ X Y f, left_derived.zero_to_self_natural _ _ _ _)

section les

def δ₀ [enough_projectives C] [preserves_finite_colimits F] (A : short_exact_sequence C) :=
δ F 0 A ≫ (left_derived.zero_iso_self F).hom.app A.1

lemma seven_term_exact_seq [enough_projectives C] [preserves_finite_colimits F]
  (A : short_exact_sequence C) :
  exact_seq D [
    (F.left_derived 1).map A.f, (F.left_derived 1).map A.g,
    δ₀ F A,
    F.map A.f, F.map A.g, (0 : F.obj A.3 ⟶ F.obj A.3)] :=
begin
  refine exact_seq.cons _ _ (exact_of_short_exact _ _ _) _ (exact_seq.cons _ _ _ _ _),
  { refine preadditive.exact_of_iso_of_exact' ((F.left_derived 1).map A.g) (δ F 0 A) _ _
      (iso.refl _) (iso.refl _) ((left_derived.zero_iso_self F).app A.1) (by simp) _ _,
    { dsimp [δ₀], rw [category.id_comp] },
    { exact (exact_iff_exact_seq _ _).2 ((six_term_exact_seq F 0 A).extract 1 2) } },
  refine exact_seq.cons _ _ _ _ _,
  { refine preadditive.exact_of_iso_of_exact' (δ F 0 A) ((F.left_derived 0).map A.f) _ _
      (iso.refl _) ((left_derived.zero_iso_self F).app A.1) ((left_derived.zero_iso_self F).app A.2)
      _ (by simp) _,
    { dsimp [δ₀], rw [category.id_comp] },
    { exact (exact_iff_exact_seq _ _).2 ((six_term_exact_seq F 0 A).extract 2 2) } },
  refine preserves_exact_seq _ (exact_seq.cons _ _ A.exact' _ ((exact_iff_exact_seq _ _).1 _)),
  refine ((abelian.tfae_epi A.3 A.g).out 0 2).1 A.epi',
end

end les

end functor.right_exact

end category_theory
