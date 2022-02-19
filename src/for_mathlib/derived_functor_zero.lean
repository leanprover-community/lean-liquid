import for_mathlib.derived_functor
import category_theory.functor_category

universes w v u

noncomputable theory

namespace category_theory

open functor

variables {C : Type u} {D : Type v} [category.{w} C] [category.{w} D]
variables (F : C ⥤ D) {A₁ A₂ A₃ X : C} {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃}
variables [abelian C] [abelian D] [additive F]

namespace limits

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

def cokernel_comparison (w : f ≫ g = 0) : cokernel f ⟶ A₃ :=
cokernel.desc f g w

end limits

namespace functor.right_exact

open limits

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

instance (ex : exact_seq C [f, g, (0 : A₃ ⟶ X)]) :
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

/-- The morphism `cokernel (kernel.lift g f) ⟶ cokernel f` assuming `f ≫ g = 0`. -/
@[simp] def cokernel_lift_to_cokernel {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
  cokernel (kernel.lift g f w) ⟶ cokernel f :=
cokernel.desc _ ((kernel.ι g) ≫ cokernel.π _) (by simp)

/-- The morphism `cokernel f ⟶ cokernel (kernel.lift (0 : Y ⟶ Z) f)`. -/
@[simp] def cokernel_to_cokernel_lift {X Y Z : C} (f : X ⟶ Y) :
  cokernel f ⟶ cokernel (kernel.lift (0 : Y ⟶ Z) f (by simp)) :=
cokernel.map _ _ (𝟙 _) (kernel.lift _ (𝟙 _) (by simp)) (by { ext, simp })

/-- The isomorphism `cokernel f ≅ cokernel (kernel.lift (0 : Y ⟶ Z) f)`. -/
def cokernel_lift_iso_cokernel {X Y Z : C} (f : X ⟶ Y) :
  cokernel (kernel.lift (0 : Y ⟶ Z) f (by simp)) ≅ cokernel f :=
{ hom := cokernel_lift_to_cokernel (by simp),
  inv := cokernel_to_cokernel_lift f,
  hom_inv_id' :=
  begin
    ext,
    simp only [cokernel_lift_to_cokernel, cokernel_to_cokernel_lift, coequalizer_as_cokernel,
      cokernel.π_desc_assoc, category.assoc, cokernel.π_desc, category.comp_id],
    rw [← kernel_zero_iso_source_hom, ← kernel_zero_iso_source_inv, ← category.assoc,
      iso.hom_inv_id, category.id_comp],
  end,
  inv_hom_id' := by { ext, simp } }

/-- The isomorphism `cokernel f ⟶ homology f (0 : Y ⟶ Z)`. -/
@[simp] def homology_iso_cokernel {X Y Z : C} (f : X ⟶ Y) :
  homology f (0 : Y ⟶ Z) (by simp) ≅ cokernel f :=
homology_iso_cokernel_lift _ _ _ ≪≫ cokernel_lift_iso_cokernel f

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

/-- The iso `(F.left_derived 0).obj X ≅ F.obj X`. -/
def functor.left_derived.zero_iso [enough_projectives C] [limits.preserves_finite_colimits F] :
  (F.left_derived 0).obj X ≅ F.obj X :=
begin
  let P := ProjectiveResolution.of X,
  refine (left_derived_obj_iso F 0 P) ≪≫ (_ ≪≫ (as_iso $ cokernel_comparison $ comp_eq_zero $
    short_exact_of_resolution_functor F P)),
  show homology _ _ _ ≅ _,
  convert homology_iso_cokernel _,
  simp
end

def functor.left_derived.zero_to_self [enough_projectives C] : nat_trans (F.left_derived 0) F :=
{ app := λ X, ((left_derived_obj_iso F 0 (ProjectiveResolution.of X)).hom) ≫
    (homology_iso_cokernel_lift _ _ _).hom ≫ cokernel_lift_to_cokernel _ ≫
    (cokernel.desc _ (F.map ((ProjectiveResolution.of X).π.f 0))
    begin
      have : (complex_shape.down ℕ).rel 1 0 := rfl,
      rw [homological_complex.d_to_eq _ this, map_homological_complex_obj_d, category.assoc,
      ← functor.map_comp],
      simp
    end),
  naturality' := sorry }

end functor.right_exact

end category_theory
