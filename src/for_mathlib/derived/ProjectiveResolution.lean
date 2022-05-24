import for_mathlib.derived.K_projective
import for_mathlib.derived.example

.

open category_theory

namespace homology

universes v u
variables {A : Type u} [category.{v} A] [abelian A]
  {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)

lemma desc_zero (w) :
  homology.desc' (0 : X ⟶ Y) g w (limits.kernel.ι _) (by simp) =
  homology.ι _ _ _ ≫ limits.cokernel.desc _ (𝟙 _) (by simp) :=
begin
  apply homology.hom_from_ext,
  simp,
end

lemma lift_desc'_of_eq_zero (hf : f = 0) :
  homology.lift f g w
    (limits.kernel.ι g ≫ limits.cokernel.π f) (by simp) ≫
    homology.desc' _ _ _ (limits.kernel.ι g) (by simp [hf]) =
  limits.kernel.ι _ :=
begin
  subst hf,
  rw desc_zero,
  simp,
end

end homology

namespace category_theory.ProjectiveResolution

open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

variables {X : A} (P : ProjectiveResolution X)

noncomputable theory

def bhc : bounded_homotopy_category A :=
chain_complex.to_bounded_homotopy_category.obj P.complex

def bhc_π : P.bhc ⟶ (bounded_homotopy_category.single _ 0).obj X :=
chain_complex.to_bounded_homotopy_category.map P.π ≫
  ((homotopy_category.quotient _ _).map_iso
  ((chain_complex.single₀_comp_embed_iso_single).app X)).hom

instance [enough_projectives A] : homotopy_category.is_quasi_iso P.bhc_π :=
begin
  dsimp only [bhc_π],
  suffices : homotopy_category.is_quasi_iso
    (chain_complex.to_bounded_homotopy_category.map P.π),
  { resetI, apply_instance },
  exact P.is_projective_resolution.is_quasi_iso_embed,
end

instance [enough_projectives A] : homotopy_category.is_K_projective P.bhc.val :=
chain_complex.to_bounded_homotopy_category.is_K_projective _ X P.π
  P.is_projective_resolution

def Ext_iso [enough_projectives A] (Y : bounded_homotopy_category A) (i : ℤ) :
  ((bounded_homotopy_category.Ext i).obj
    (opposite.op ((bounded_homotopy_category.single _ 0).obj X))).obj Y ≅
  (preadditive_yoneda.obj (Y⟦i⟧)).obj (opposite.op P.bhc) :=
by apply bounded_homotopy_category.Ext_iso _ _ _ _ P.bhc_π

def Ext_iso_zero [enough_projectives A] (Y : bounded_homotopy_category A) :
  ((bounded_homotopy_category.Ext 0).obj
    (opposite.op ((bounded_homotopy_category.single _ 0).obj X))).obj Y ≅
  (preadditive_yoneda.obj Y).obj (opposite.op P.bhc) :=
P.Ext_iso Y 0 ≪≫ (preadditive_yoneda.map_iso (shift_zero _ _)).app _

def Ext_single_iso [enough_projectives A] (Y : A) :
  ((bounded_homotopy_category.Ext 0).obj
    (opposite.op ((bounded_homotopy_category.single _ 0).obj X))).obj
    ((bounded_homotopy_category.single _ 0).obj Y) ≅
    (((preadditive_yoneda.obj Y).map_homological_complex _).obj
      P.bhc.val.as.op).homology 0 :=
P.Ext_iso_zero _ ≪≫ P.bhc.hom_single_iso Y 0

lemma is_zero_hom_of_is_zero {X Y : A} (hX : is_zero X) :
  is_zero (AddCommGroup.of (X ⟶ Y)) :=
{ unique_to := λ Z,
  begin
    refine ⟨{to_inhabited := infer_instance, uniq := λ f, _}⟩,
    ext x,
    rw [hX.eq_to x, ← hX.eq_to (0 : X ⟶ Y), map_zero, map_zero]
  end,
  unique_from := λ Z,
  begin
    refine ⟨{to_inhabited := infer_instance, uniq := λ f, _}⟩,
    ext z,
    rw [hX.eq_to (f z), ← hX.eq_to _]
  end }

def homology_zero_iso [enough_projectives A] (Y : A) :
    (((preadditive_yoneda.obj Y).map_homological_complex _).obj
      P.bhc.val.as.op).homology 0 ≅
    kernel ((preadditive_yoneda.obj Y).map (P.complex.d 1 0).op) :=
homology_iso _ (1 : ℤ) 0 (-1) (by simp) (by simp) ≪≫
{ hom := kernel.lift _
    (homology.desc' _ _ _ (kernel.ι _) begin
      rw kernel.lift_ι,
      apply is_zero.eq_of_src,
      apply is_zero_hom_of_is_zero,
      exact is_zero_zero _,
    end) begin
      apply homology.hom_from_ext,
      simp only [homology.π'_desc'_assoc, comp_zero],
      erw kernel.condition,
    end,
  inv := homology.lift _ _ _
    (kernel.ι _ ≫ cokernel.π _)
    begin
      simp only [functor.map_homological_complex_obj_d,
        homological_complex.op_d, category.assoc, cokernel.π_desc],
      erw kernel.condition,
    end,
  hom_inv_id' := begin
    apply homology.hom_to_ext,
    apply homology.hom_from_ext,
    simp,
  end,
  inv_hom_id' := begin
    apply equalizer.hom_ext,
    simp only [category.assoc, kernel.lift_ι, equalizer_as_kernel, category.id_comp],
    apply homology.lift_desc'_of_eq_zero,
    apply is_zero.eq_of_src,
    apply is_zero_hom_of_is_zero,
    exact is_zero_zero _,
  end }

def Ext_single_iso_kernel [enough_projectives A] (Y : A) :
  ((bounded_homotopy_category.Ext 0).obj
    (opposite.op ((bounded_homotopy_category.single _ 0).obj X))).obj
    ((bounded_homotopy_category.single _ 0).obj Y) ≅
    kernel ((preadditive_yoneda.obj Y).map (P.complex.d 1 0).op) :=
P.Ext_single_iso Y ≪≫ P.homology_zero_iso _

def hom_to_kernel [enough_projectives A] (Y : A) :
  (preadditive_yoneda.obj Y).obj (opposite.op X) ⟶
  kernel ((preadditive_yoneda.obj Y).map (P.complex.d 1 0).op) :=
kernel.lift _ (category_theory.functor.map _ $ quiver.hom.op $ P.π.f _)
sorry

instance mono_hom_to_kernel [enough_projectives A] (Y : A) :
  category_theory.mono (hom_to_kernel P Y) := sorry

instance epi_hom_to_kernel [enough_projectives A] (Y : A) :
  category_theory.epi (hom_to_kernel P Y) := sorry

instance is_iso_hom_to_kernel [enough_projectives A] (Y : A) :
  is_iso (hom_to_kernel P Y) := is_iso_of_mono_of_epi _

def Ext_single_iso_hom [enough_projectives A] (Y : A) :
  ((bounded_homotopy_category.Ext 0).obj
    (opposite.op ((bounded_homotopy_category.single _ 0).obj X))).obj
    ((bounded_homotopy_category.single _ 0).obj Y) ≅
  (preadditive_yoneda.obj Y).obj (opposite.op X) :=
P.Ext_single_iso_kernel Y ≪≫ (as_iso (P.hom_to_kernel Y)).symm

end category_theory.ProjectiveResolution
