import category_theory.abelian.homology
import for_mathlib.homotopy_category_pretriangulated
import category_theory.limits.constructions.epi_mono
import for_mathlib.homology_iso
import for_mathlib.homotopy_category_coproducts
import category_theory.abelian.homology

namespace category_theory

open category_theory.limits

universes v u

class AB4 (A : Type u) [category.{v} A] [has_coproducts A] : Prop :=
(cond : ∀ {α : Type v} (X Y : α → A) (f : Π a, X a ⟶ Y a)
  (hf : ∀ a, mono (f a)), mono (sigma.desc $ λ a, f a ≫ sigma.ι Y a))

variables {A : Type u} [category.{v} A]

instance AB4_mono
  [has_coproducts A] [AB4 A]
  {α : Type v} (X Y : α → A) (f : Π a, X a ⟶ Y a)
  [∀ a, mono (f a)] : mono (sigma.desc $ λ a, f a ≫ sigma.ι Y a) :=
begin
  apply AB4.cond, assumption,
end

variable (A)
noncomputable
def sigma_functor
  [has_coproducts A]
  (α : Type v) : (α → A) ⥤ A :=
{ obj := λ X, sigma_obj X,
  map := λ X Y f, sigma.desc $ λ a, f a ≫ sigma.ι _ a } .
variable {A}

instance sigma_functor_preserves_mono
  [has_coproducts A] [AB4 A]
  (α : Type v)
  {X Y : α → A} (f : X ⟶ Y) [∀ a, mono (f a)] :
  mono ((sigma_functor A α).map f) :=
category_theory.AB4_mono X Y f

instance sigma_functor_preserves_epi
  [has_coproducts A]
  (α : Type v)
  {X Y : α → A} (f : X ⟶ Y) [∀ a, epi (f a)] :
  epi ((sigma_functor A α).map f) :=
begin
  constructor, intros Z s t h,
  apply colimit.hom_ext,
  intros a,
  dsimp [sigma_functor] at h,
  apply_fun (λ e, colimit.ι _ a ≫ e) at h,
  simp at h,
  rwa cancel_epi at h,
end

lemma AB4_of_preserves_colimits_of_reflects_limits_of_AB4
  {A B : Type u} [category.{v} A] [category.{v} B]
  [has_coproducts A]
  [has_coproducts B]
  (F : A ⥤ B)
  [preserves_colimits F]
  [creates_limits F]
  [has_limits B]
  [AB4 B] : AB4 A :=
begin
  constructor, introsI a X Y f hf,
  let t := _, change mono t,
  suffices : mono (F.map t),
  { resetI, apply reflects_mono F },
  let eX : F.obj (∐ λ (a : a), X a) ≅ (∐ λ a, F.obj (X a)) :=
    (is_colimit_of_preserves F (colimit.is_colimit _)).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫ has_colimit.iso_of_nat_iso
      (nat_iso.of_components (λ _, iso.refl _) _),
  swap, { rintro i _ ⟨⟨⟨⟩⟩⟩, dsimp, simp, dsimp, simp },
  let eY : F.obj (∐ λ (a : a), Y a) ≅ (∐ λ a, F.obj (Y a)) :=
    (is_colimit_of_preserves F (colimit.is_colimit _)).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫ has_colimit.iso_of_nat_iso
      (nat_iso.of_components (λ _, iso.refl _) _),
  swap, { rintro i _ ⟨⟨⟨⟩⟩⟩, dsimp, simp, dsimp, simp },
  let tt : (∐ λ a, F.obj (X a)) ⟶ (∐ λ a, F.obj (Y a)) :=
    sigma.desc (λ a, F.map (f a) ≫ sigma.ι _ a),
  haveI : mono tt,
  { apply AB4.cond, intros a,
    apply category_theory.preserves_mono F },
  suffices : F.map t = eX.hom ≫ tt ≫ eY.inv,
  { rw this, apply mono_comp },
  apply (is_colimit_of_preserves F (colimit.is_colimit _)).hom_ext,
  swap, apply_instance,
  intros i,
  erw [← F.map_comp, colimit.ι_desc, F.map_comp],
  dsimp [eX, tt, t, eY, limits.is_colimit.cocone_point_unique_up_to_iso, is_colimit_of_preserves,
    has_colimit.iso_of_nat_iso, is_colimit.map],
  slice_rhs 0 1
  { erw (is_colimit_of_preserves F (colimit.is_colimit _)).fac },
  slice_rhs 0 1
  { erw colimit.ι_desc },
  dsimp [iso.refl],
  simp,
end

noncomputable
example {X Y Z : A} [abelian A]
  (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0): cokernel (image_to_kernel' f g w) ≅ homology f g w :=
  (homology_iso_cokernel_image_to_kernel' f g w).symm

noncomputable
def coproduct_kernel_comparison (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts A] (i : M) (X : α → homological_complex A S) :
  (∐ λ (a : α), kernel ((X a).d_from i)) ⟶ kernel ((∐ X).d_from i) :=
sigma.desc $ λ a, kernel.lift _ (kernel.ι _ ≫ (sigma.ι _ a : X a ⟶ ∐ X).f i) sorry

-- This should follow from the AB4 assumption
instance is_iso_coproduct_kernel_comparison (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts A] [AB4 A] (i : M) (X : α → homological_complex A S) :
is_iso (coproduct_kernel_comparison M S α i X) := sorry

noncomputable
def coproduct_homology_comparison (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts A] (i : M) (X : α → homological_complex A S) :
  (∐ λ a : α, (X a).homology i) ⟶ (∐ X).homology i :=
sigma.desc $ λ b, (homology_functor _ _ _).map $ sigma.ι _ _

noncomputable
def coproduct_homology_comparison_inv (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts A] [AB4 A] (i : M) (X : α → homological_complex A S) :
  (∐ X).homology i ⟶ (∐ λ a : α, (X a).homology i) :=
homology.desc' _ _ _ (inv (coproduct_kernel_comparison M S α i X) ≫
  sigma.desc (λ b, homology.π' ((X b).d_to _) ((X b).d_from i) sorry ≫ sigma.ι _ b)) sorry

noncomputable
def coproduct_homology_iso
  (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts A] [AB4 A] (i : M) (X : α → homological_complex A S) :
  (∐ λ a : α, (X a).homology i) ≅ (∐ X).homology i :=
{ hom := coproduct_homology_comparison _ _ _ _ _,
  inv := coproduct_homology_comparison_inv _ _ _ _ _,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

noncomputable
def is_colimit_homology_map_cocone  (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts A] [AB4 A] (i : M) (X : α → homological_complex A S) :
  is_colimit ((homology_functor A S i).map_cocone (colimit.cocone (discrete.functor X))) :=
{ desc := λ E, (coproduct_homology_iso _ _ _ _ _).inv ≫ sigma.desc (λ a, E.ι.app _),
  fac' := sorry,
  uniq' := sorry }

noncomputable
instance homology_functor_preserves_coproducts
  (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts A] [AB4 A] (i) :
  preserves_colimits_of_shape (discrete α)
  (homology_functor A S i) :=
begin
  constructor, intros K,
  let E : K ≅ discrete.functor K.obj := discrete.nat_iso (λ i, iso.refl _),
  suffices : preserves_colimit (discrete.functor K.obj) (homology_functor A _ i),
  { apply preserves_colimit_of_iso_diagram _ E.symm, assumption },
  apply preserves_colimit_of_preserves_colimit_cocone
    (colimit.is_colimit (discrete.functor K.obj)),
  apply is_colimit_homology_map_cocone,
end

noncomputable
def is_colimit_homotopy_category_homology_functor_map_cocone
  {α : Type v} [abelian A] [has_coproducts A] [AB4 A] (i)
  (K : α → homotopy_category A (complex_shape.up ℤ)) :
  is_colimit
  ((homotopy_category.homology_functor A (complex_shape.up ℤ) i).map_cocone
    (homotopy_category.colimit_cofan K)) :=
{ desc := λ S,
    (is_colimit_of_preserves (homology_functor A (complex_shape.up ℤ) i)
    (colimit.is_colimit $ discrete.functor $ λ i, (K i).as)).desc ⟨S.X,
    discrete.nat_trans $ λ i, S.ι.app i⟩,
  fac' := begin
    intros S j, dsimp,
    erw (is_colimit_of_preserves (homology_functor A (complex_shape.up ℤ) i)
      (colimit.is_colimit (discrete.functor (λ (i : α), (K i).as)))).fac,
    refl,
  end,
  uniq' := begin
    intros S m hm,
    apply (is_colimit_of_preserves (homology_functor A (complex_shape.up ℤ) i)
      (colimit.is_colimit (discrete.functor (λ (i : α), (K i).as)))).hom_ext,
    intros j,
    erw (is_colimit_of_preserves (homology_functor A (complex_shape.up ℤ) i)
      (colimit.is_colimit (discrete.functor (λ (i : α), (K i).as)))).fac,
    dsimp, rw ← hm, refl,
  end }

noncomputable
instance homotopy_category_homology_functor_preserves_coproducts
  (α : Type v)
  [abelian A] [has_coproducts A] [AB4 A] (i) :
  preserves_colimits_of_shape (discrete α)
  (homotopy_category.homology_functor A (complex_shape.up ℤ) i) :=
begin
  constructor, intros K,
  let E : K ≅ discrete.functor K.obj := discrete.nat_iso (λ i, iso.refl _),
  suffices : preserves_colimit (discrete.functor K.obj) (homotopy_category.homology_functor A _ i),
  { apply preserves_colimit_of_iso_diagram _ E.symm, assumption },
  apply preserves_colimit_of_preserves_colimit_cocone
    (homotopy_category.is_colimit_cofan K.obj),
  apply is_colimit_homotopy_category_homology_functor_map_cocone,
end

end category_theory
