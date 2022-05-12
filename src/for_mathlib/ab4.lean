import category_theory.abelian.homology
import for_mathlib.homotopy_category_pretriangulated
import category_theory.limits.constructions.epi_mono
import for_mathlib.homology_iso

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

instance (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts A] [AB4 A] (i) :
  preserves_colimits_of_shape (discrete α)
  (homology_functor A S i) := sorry

instance (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts A] [AB4 A] (i) :
  preserves_colimits_of_shape (discrete α)
  (homotopy_category.homology_functor A S i) := sorry

end category_theory
