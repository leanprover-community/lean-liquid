import for_mathlib.derived_functor

universes w v u

noncomputable theory

section right_exact

namespace category_theory

open functor limits

variables {C : Type u} {D : Type v} [category.{w} C] [category.{w} D] [abelian C] [abelian D]
variables (F : C ⥤ D) [additive F] {X : C}
variables [limits.preserves_finite_colimits F]

/-- The morphism `cokernel (kernel.lift (0 : Y ⟶ Z) f) ⟶ cokernel f`. -/
@[simp] def cokernel_lift_to_cokernel {X Y Z : C} (f : X ⟶ Y) :
  cokernel (kernel.lift (0 : Y ⟶ Z) f (by simp)) ⟶ cokernel f :=
cokernel.desc _ ((kernel.ι 0) ≫ cokernel.π _) (by simp)

/-- The morphism `cokernel f ⟶ cokernel (kernel.lift (0 : Y ⟶ Z) f)`. -/
@[simp] def cokernel_to_cokernel_lift {X Y Z : C} (f : X ⟶ Y) :
  cokernel f ⟶ cokernel (kernel.lift (0 : Y ⟶ Z) f (by simp)) :=
cokernel.map _ _ (𝟙 _) (kernel.lift _ (𝟙 _) (by simp)) (by { ext, simp })

/-- The isomorphism `cokernel f ≅ cokernel (kernel.lift (0 : Y ⟶ Z) f)`. -/
def cokernel_lift_iso_cokernel {X Y Z : C} (f : X ⟶ Y) :
  cokernel (kernel.lift (0 : Y ⟶ Z) f (by simp)) ≅ cokernel f :=
{ hom := cokernel_lift_to_cokernel f,
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
def cokernel_homology_iso {X Y Z : C} (f : X ⟶ Y) :
  homology f (0 : Y ⟶ Z) (by simp) ≅ cokernel f :=
homology_iso_cokernel_lift _ _ _ ≪≫ cokernel_lift_iso_cokernel f

lemma short_exact_of_resolution (P: ProjectiveResolution X) : exact_seq C
  [P.complex.d 1 0, P.π.f 0, (0 : X ⟶ X)] :=
begin
  refine exact_seq.cons _ _ P.exact₀ _ _,
  rw ← exact_iff_exact_seq,
  exact ((abelian.tfae_epi X (P.π.f 0)).out 0 2).1 P.epi
end

lemma short_exact_of_resolution_functor (P: ProjectiveResolution X) : exact_seq D
  [((F.map_homological_complex (complex_shape.down ℕ)).obj P.complex).d_to 0,
  F.map (P.π.f 0), (0 : F.obj X ⟶ F.obj X)] :=
begin
  refine exact_seq.cons _ _ _ _ _,
  { have : (complex_shape.down ℕ).rel 1 0 := rfl,
    let f := (homological_complex.X_prev_iso ((F.map_homological_complex _).obj P.complex) this),
    simp at this,
    refine preadditive.exact_of_iso_of_exact' (F.map (P.complex.d 1 0)) (F.map (P.π.f 0)) _ _
      f.symm (iso.refl _) (iso.refl _) (by simp) (by simp) _,
    exact (exact_iff_exact_seq _ _ ).2
      ((right_exact.preserves_exact_seq F (short_exact_of_resolution P)).extract 0 2) },
  rw ← exact_iff_exact_seq,
  refine ((abelian.tfae_epi (F.obj X) (F.map (P.π.f 0))).out 0 2).1
    (category_theory.preserves_epi F _),
end

/-- The iso `(F.left_derived 0).obj X ≅ F.obj X`. -/
def functor.left_derived.zero_iso [enough_projectives C] : (F.left_derived 0).obj X ≅ F.obj X :=
begin
  let P := ProjectiveResolution.of X,
  refine (left_derived_obj_iso F 0 P) ≪≫ (_ ≪≫ (as_iso $ right_exact.cokernel_comparison
    $ short_exact_of_resolution_functor F P)),
  show homology _ _ _ ≅ _,
  convert cokernel_homology_iso _,
  simp
end

end category_theory

end right_exact
