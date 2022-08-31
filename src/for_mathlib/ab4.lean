import category_theory.abelian.homology
import for_mathlib.homotopy_category_pretriangulated
import category_theory.limits.constructions.epi_mono
import for_mathlib.homology_iso
import for_mathlib.homotopy_category_coproducts
import category_theory.abelian.homology

namespace category_theory

open category_theory.limits

universes v u

class AB4 (A : Type u) [category.{v} A] [has_coproducts.{v} A] : Prop :=
(cond : ∀ {α : Type v} (X Y : α → A) (f : Π a, X a ⟶ Y a)
  (hf : ∀ a, mono (f a)), mono (sigma.desc $ λ a, f a ≫ sigma.ι Y a))

variables {A : Type u} [category.{v} A]

instance AB4_mono
  [has_coproducts.{v} A] [AB4 A]
  {α : Type v} (X Y : α → A) (f : Π a, X a ⟶ Y a)
  [∀ a, mono (f a)] : mono (sigma.desc $ λ a, f a ≫ sigma.ι Y a) :=
begin
  apply AB4.cond, assumption,
end

variable (A)
noncomputable
def sigma_functor
  [has_coproducts.{v} A]
  (α : Type v) : (α → A) ⥤ A :=
{ obj := λ X, sigma_obj X,
  map := λ X Y f, sigma.desc $ λ a, f a ≫ sigma.ι _ a,
  map_id' := λ X, by { ext ⟨j⟩, simp },
  map_comp' := λ X Y Z f j, by { ext ⟨j⟩, simp } }.

variable {A}

instance sigma_functor_preserves_mono
  [has_coproducts.{v} A] [AB4 A]
  (α : Type v)
  {X Y : α → A} (f : X ⟶ Y) [∀ a, mono (f a)] :
  mono ((sigma_functor A α).map f) :=
category_theory.AB4_mono X Y f

instance sigma_functor_preserves_epi
  [has_coproducts.{v} A]
  (α : Type v)
  {X Y : α → A} (f : X ⟶ Y) [∀ a, epi (f a)] :
  epi ((sigma_functor A α).map f) :=
begin
  constructor, intros Z s t h,
  apply colimit.hom_ext,
  rintros ⟨a⟩,
  dsimp [sigma_functor] at h,
  apply_fun (λ e, colimit.ι _ (discrete.mk a) ≫ e) at h,
  simp at h,
  rwa cancel_epi at h,
end

set_option pp.universes true

lemma AB4_of_preserves_colimits_of_reflects_limits_of_AB4
  {A B : Type u} [category.{v} A] [category.{v} B]
  [has_coproducts.{v} A]
  [has_coproducts.{v} B]
  (F : A ⥤ B)
  [preserves_colimits F]
  [creates_limits F]
  [has_limits B]
  [AB4 B] : AB4 A :=
begin
  constructor, introsI a X Y f hf,
  let t := _, change mono t,
  suffices : mono (F.map t),
  { haveI := reflects_limits_of_size_shrink.{0 v 0 v} F,
    apply F.mono_of_mono_map this, },
  let eX : F.obj (∐ λ (a : a), X a) ≅ (∐ λ a, F.obj (X a)) :=
    (is_colimit_of_preserves F (colimit.is_colimit _)).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫ has_colimit.iso_of_nat_iso
      (nat_iso.of_components (λ _, iso.refl _) _),
  swap, { rintro ⟨⟩ ⟨⟩ ⟨⟨⟨⟩⟩⟩, dsimp, simp, dsimp, simp },
  let eY : F.obj (∐ λ (a : a), Y a) ≅ (∐ λ a, F.obj (Y a)) :=
    (is_colimit_of_preserves F (colimit.is_colimit _)).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫ has_colimit.iso_of_nat_iso
      (nat_iso.of_components (λ _, iso.refl _) _),
  swap, { rintro ⟨⟩ ⟨⟩ ⟨⟨⟨⟩⟩⟩, dsimp, simp, dsimp, simp },
  let tt : (∐ λ a, F.obj (X a)) ⟶ (∐ λ a, F.obj (Y a)) :=
    sigma.desc (λ a, F.map (f a) ≫ sigma.ι _ a),
  haveI : mono tt,
  { apply AB4.cond, intros a, apply_instance },
  suffices : F.map t = eX.hom ≫ tt ≫ eY.inv,
  { rw this, apply mono_comp },
  apply (is_colimit_of_preserves F (colimit.is_colimit _)).hom_ext,
  swap, apply_instance,
  rintros ⟨i⟩,
  erw [← F.map_comp, colimit.ι_desc, F.map_comp],
  dsimp [eX, tt, t, eY, limits.is_colimit.cocone_point_unique_up_to_iso, is_colimit_of_preserves,
    has_colimit.iso_of_nat_iso, is_colimit.map],
  slice_rhs 0 1
  { erw (is_colimit_of_preserves F (colimit.is_colimit _)).fac },
  slice_rhs 0 1
  { erw colimit.ι_desc },
  dsimp [iso.refl],
  simp only [category.id_comp, colimit.ι_desc, cofan.mk_ι_app, category.assoc,
    cocones.precompose_obj_ι, nat_trans.comp_app, nat_iso.of_components_inv_app,
    colimit.cocone_ι, functor.map_cocone_ι_app],
  dsimp,
  simp,
end

noncomputable
example {X Y Z : A} [abelian A]
  (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0): cokernel (image_to_kernel' f g w) ≅ homology f g w :=
  (homology_iso_cokernel_image_to_kernel' f g w).symm

noncomputable
def coproduct_kernel_comparison (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts.{v} A] (i : M) (X : α → homological_complex A S) :
  (∐ λ (a : α), kernel ((X a).d_from i)) ⟶ kernel ((∐ X).d_from i) :=
sigma.desc $ λ a, kernel.lift _ (kernel.ι _ ≫ (sigma.ι _ a : X a ⟶ ∐ X).f i)
begin
  rw [category.assoc, (sigma.ι X a : X a ⟶ _).comm_from, ← category.assoc, kernel.condition,
    zero_comp],
end

-- This should follow from the AB4 assumption
instance mono_coproduct_kernel_comparison (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts.{v} A] [AB4 A] (i : M) (X : α → homological_complex A S) :
mono (coproduct_kernel_comparison M S α i X) :=
begin
  let ι : kernel ((∐ X).d_from i) ⟶ _ := kernel.ι _,
  let t := _, change (mono t),
  suffices : mono (t ≫ ι),
  { resetI, apply mono_of_mono t ι },
  let F : homological_complex A S ⥤ A := homological_complex.eval _ _ i,
  let E : (∐ X).X i ≅ (∐ λ b, (X b).X i) :=
    (is_colimit_of_preserves F (colimit.is_colimit
      (discrete.functor X))).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ b, iso.refl _),
  suffices : t ≫ ι = sigma.desc (λ a, kernel.ι _ ≫ (sigma.ι (λ b, (X b).X i) a)) ≫ E.inv,
  { rw this, apply_instance },
  dsimp [t,ι, coproduct_kernel_comparison],
  apply colimit.hom_ext, intros a,
  simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, kernel.lift_ι, category.assoc,
    has_colimit.iso_of_nat_iso_ι_inv_assoc, discrete.nat_iso_inv_app,
    colimit.comp_cocone_point_unique_up_to_iso_inv, functor.map_cocone_ι_app,
    colimit.cocone_ι, homological_complex.eval_map],
  dsimp, simp only [category.id_comp],
end

noncomputable
def eval_next (A : Type u) [category.{v} A] [abelian A] {M : Type*}
  (S : complex_shape M) (i : M) :
  homological_complex A S ⥤ A :=
{ obj := λ X, X.X_next i,
  map := λ X Y f, f.next i,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl, }

open_locale zero_object

noncomputable
def preserves_colimits_of_shape_const_zero_aux
  (α : Type v) (M : Type*) (S : complex_shape M)
  [abelian A] [has_coproducts.{v} A]
  (K : discrete α ⥤ homological_complex A S) :
  is_colimit (((functor.const _).obj (0 : A)).map_cocone (colimit.cocone K)) :=
{ desc := λ S, 0,
  fac' := λ S j, (is_zero_zero _).eq_of_src _ _,
  uniq' := λ S m hm, (is_zero_zero _).eq_of_src _ _ }

noncomputable
instance preserves_colimits_of_shape_const_zero
  (α : Type v) (M : Type*) (S : complex_shape M) [abelian A] [has_coproducts.{v} A] :
  preserves_colimits_of_shape (discrete α)
  ((functor.const _).obj 0 : homological_complex A S ⥤ A) :=
begin
  constructor, intros K,
  apply preserves_colimit_of_preserves_colimit_cocone
    (colimit.is_colimit K),
  apply preserves_colimits_of_shape_const_zero_aux,
end

noncomputable
def eval_next_iso
  (M : Type*) (S : complex_shape M) [abelian A] (i : M) :
  eval_next A S i ≅ homological_complex.eval _ _ (S.next i) :=
nat_iso.of_components (λ X, iso.refl _)
begin
  intros X Y f,
  simp only [iso.refl_hom, category.comp_id, homological_complex.eval_map, category.id_comp],
  refl
end

noncomputable
instance eval_next_preserves_coproducts (α : Type v)
  (M : Type*) (S : complex_shape M) [abelian A] [has_coproducts.{v} A] (i : M) :
  preserves_colimits_of_shape (discrete α) (eval_next A S i) :=
begin
  apply preserves_colimits_of_shape_of_nat_iso (eval_next_iso M S i).symm,
  apply_instance
end

noncomputable
def eval_prev (A : Type u) [category.{v} A] [abelian A] {M : Type*}
  (S : complex_shape M) (i : M) :
  homological_complex A S ⥤ A :=
{ obj := λ X, X.X_prev i,
  map := λ X Y f, f.prev i,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl, }

noncomputable
def eval_prev_iso
  (M : Type*) (S : complex_shape M) [abelian A] (i : M) :
  eval_prev A S i ≅ homological_complex.eval _ _ (S.prev i) :=
nat_iso.of_components (λ X, iso.refl _)
begin
  intros X Y f,
  simp only [iso.refl_hom, category.comp_id, homological_complex.eval_map, category.id_comp],
  refl,
end

noncomputable
instance eval_prev_preserves_coproducts (α : Type v)
  (M : Type*) (S : complex_shape M) [abelian A] [has_coproducts.{v} A] (i : M) :
  preserves_colimits_of_shape (discrete α) (eval_prev A S i) :=
begin
  apply preserves_colimits_of_shape_of_nat_iso (eval_prev_iso M S i).symm,
  apply_instance
end

lemma exact_iff_exact_cokernel_desc [abelian A] (X Y Z : A)
  (f : X ⟶ Y) (g : Y ⟶ Z) :
  exact f g ↔ ∃ w, mono (cokernel.desc f g w) :=
begin
  split,
  { intros h, refine ⟨h.w, _⟩,
    apply abelian.pseudoelement.mono_of_zero_of_map_zero,
    intros a ha,
    have h' : exact f (cokernel.π f) := abelian.exact_cokernel f,
    replace h' := abelian.pseudoelement.pseudo_exact_of_exact h',
    have hπ := abelian.pseudoelement.pseudo_surjective_of_epi (cokernel.π f),
    obtain ⟨b,rfl⟩ := hπ a,
    rw [← abelian.pseudoelement.comp_apply, cokernel.π_desc] at ha,
    replace h := abelian.pseudoelement.pseudo_exact_of_exact h,
    obtain ⟨b,rfl⟩ := h.2 _ ha,
    rw [← abelian.pseudoelement.comp_apply, cokernel.condition],
    simp only [abelian.pseudoelement.zero_apply] },
  { rintros ⟨w,h⟩, rw abelian.exact_iff, refine ⟨w, _⟩, resetI,
    rw ← cancel_mono (cokernel.desc f g w),
    simp only [category.assoc, cokernel.π_desc, kernel.condition, zero_comp] }
end

lemma exact_iff_exact_of_cofork [abelian A] (X Y Z : A)
  (f : X ⟶ Y) (g : Y ⟶ Z) (T : cokernel_cofork f) (hT : is_colimit T) :
  exact f g ↔ ∃ w : f ≫ g = 0,
  mono (hT.desc (cokernel_cofork.of_π g w)) :=
begin
  let e : T.X ≅ cokernel f :=
    hT.cocone_point_unique_up_to_iso (colimit.is_colimit _),
  rw exact_iff_exact_cokernel_desc,
  apply exists_congr (λ w, _),
  have : hT.desc (cokernel_cofork.of_π g w) =
    e.hom ≫ cokernel.desc f g w,
  { dsimp [e, limits.is_colimit.cocone_point_unique_up_to_iso],
    apply hT.hom_ext, intros i,
    simp only [is_colimit.fac, is_colimit.fac_assoc, colimit.cocone_ι,
      colimit.ι_desc] },
  rw this,
  split,
  { introI _, apply_instance },
  { introI, constructor,
    intros Z a b h,
    rw [← cancel_mono e.inv, ← cancel_mono (e.hom ≫ cokernel.desc f g w)],
    simpa }
end

noncomputable
def sigma_cokernel_cofork [abelian A] [has_coproducts.{v} A] [AB4 A]
  {α : Type v} (X Y : α → A) (f : X ⟶ Y) :
  cokernel_cofork ((sigma_functor A α).map f) :=
cokernel_cofork.of_π
(sigma.desc (λ a : α, cokernel.π (f a) ≫ sigma.ι (λ b, cokernel (f b)) a))
begin
  apply colimit.hom_ext,
  intros a,
  dsimp [sigma_functor],
  simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc,
    colimit.ι_desc, cokernel.condition_assoc, zero_comp,
    comp_zero],
end

noncomputable
def is_colimit_sigma_cokernel_cofork [abelian A] [has_coproducts.{v} A] [AB4 A]
  {α : Type v} (X Y : α → A) (f : X ⟶ Y) :
  is_colimit (sigma_cokernel_cofork X Y f) :=
is_colimit_aux _
(λ S, sigma.desc $ λ b, cokernel.desc _ (sigma.ι _ _ ≫ S.π)
  begin
    rw ← category.assoc,
    let t := _, change t ≫ _ = _,
    have ht : t = sigma.ι X b ≫ (sigma_functor A α).map f,
    { dsimp [sigma_functor], simp },
    rw ht, clear ht, clear t,
    rw [category.assoc, S.condition, comp_zero],
  end)
begin
  intros S,
  dsimp [sigma_cokernel_cofork],
  apply colimit.hom_ext,
  simp only [category.assoc, colimit.ι_desc, cofan.mk_ι_app, eq_self_iff_true,
    cokernel_cofork.condition, comp_zero,
    colimit.ι_desc_assoc, cokernel.π_desc, implies_true_iff],
  rintro ⟨j⟩,
  simp,
end
begin
  intros S m hm,
  apply colimit.hom_ext, rintros ⟨a⟩,
  simp only [colimit.ι_desc, cofan.mk_ι_app],
  apply coequalizer.hom_ext, simp only [coequalizer_as_cokernel, cokernel.π_desc],
  simp_rw [← hm, ← category.assoc], congr' 1,
  dsimp [sigma_cokernel_cofork],
  simp only [colimit.ι_desc, cofan.mk_ι_app],
end

lemma exact_coproduct [abelian A] [has_coproducts.{v} A] [AB4 A]
  {α : Type v} (X Y Z : α → A) (f : X ⟶ Y) (g : Y ⟶ Z)
  (w : ∀ i, exact (f i) (g i)) :
  exact ((sigma_functor A α).map f) ((sigma_functor A α).map g) :=
begin
  let ι : (λ a : α, cokernel (f a)) ⟶ Z :=
    λ a, (cokernel.desc _ (g a) (w a).w),
  let π : Y ⟶ (λ a : α, cokernel (f a)) :=
    λ a, (cokernel.π _),
  haveI : ∀ a, mono (ι a),
  { intros a,
    suffices : ∃ w, mono (cokernel.desc (f a) (g a) w),
    { obtain ⟨q,h⟩ := this, exact h },
    rw ← exact_iff_exact_cokernel_desc, apply w },
  have : mono ((sigma_functor A α).map ι),
  { apply AB4.cond, assumption },
  -- Now need to show that sigma functor commutes with cokernels
  -- Use the fact that this commutes with cokernels to identify the source
  -- with the cokernel of `f`.
  -- Then use exact_iff_exact_cokernel_desc
  rw exact_iff_exact_of_cofork
    ((sigma_functor A α).obj X)
    ((sigma_functor A α).obj Y)
    ((sigma_functor A α).obj Z)
    ((sigma_functor A α).map f)
    ((sigma_functor A α).map g)
    (sigma_cokernel_cofork _ _ f)
    (is_colimit_sigma_cokernel_cofork _ _ f),
  refine ⟨_,_⟩,
  { apply colimit.hom_ext, intros a,
    dsimp [sigma_functor],
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, colimit.ι_desc, comp_zero],
    rw [← category.assoc, (w a.1).w, zero_comp] },
  simp only [exact_iff_exact_cokernel_desc] at w,
  choose w₁ w₂ using w,
  convert AB4.cond _ Z ι w₂ using 1,
  apply colimit.hom_ext, intros a,
  dsimp [is_colimit_sigma_cokernel_cofork, is_colimit_aux],
  simp only [colimit.ι_desc, cofan.mk_ι_app],
  apply coequalizer.hom_ext,
  simp only [cokernel.π_desc, cokernel.π_desc_assoc],
  dsimp [sigma_functor],
  simp only [colimit.ι_desc, cofan.mk_ι_app],
end

section
open_locale pseudoelement
instance epi_coproduct_kernel_comparison [has_coproducts.{v} A] [AB4 A]
  (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts.{v} A] (i : M) (X : α → homological_complex A S) :
  epi (coproduct_kernel_comparison M S α i X) :=
begin
  /-
     _ -ι₁-> _ -π₁-> _
     |       |       |
     t     E.inv   Q.inv
     |       |       |
     v       v       v
     _ -ι₂-> _ -π₂-> _

  -/
  let t := _, change epi t,
  let F : homological_complex A S ⥤ A := homological_complex.eval _ _ i,
  let N : homological_complex A S ⥤ A := eval_next _ _ i,
  let E : (∐ X).X i ≅ (∐ λ b, (X b).X i) :=
    (is_colimit_of_preserves F (colimit.is_colimit
      (discrete.functor X))).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ b, iso.refl _),
  let Q : (∐ X).X_next i ≅ (∐ λ b, (X b).X_next i) :=
    (is_colimit_of_preserves N (colimit.is_colimit
      (discrete.functor X))).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ b, iso.refl _),
  let ι₁ : (∐ λ (a : α), kernel ((X a).d_from i)) ⟶ (∐ λ b, (X b).X i) :=
    sigma.desc (λ a, kernel.ι _ ≫ sigma.ι _ a),
  let π₁ : (∐ λ b, (X b).X i) ⟶ (∐ λ b, (X b).X_next i) :=
    sigma.desc (λ a, (X a).d_from i ≫ sigma.ι _ a),
  let ι₂ : kernel ((∐ X).d_from i) ⟶ (∐ X).X i := kernel.ι _,
  let π₂ : (∐ X).X i ⟶ (∐ X).X_next i := (∐ X).d_from i,
  have sqι : ι₁ ≫ E.inv = t ≫ ι₂,
  { apply colimit.hom_ext, intros a, dsimp [ι₁, E, t, ι₂],
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc,
      has_colimit.iso_of_nat_iso_ι_inv_assoc, discrete.nat_iso_inv_app,
      colimit.comp_cocone_point_unique_up_to_iso_inv, functor.map_cocone_ι_app,
      colimit.cocone_ι, homological_complex.eval_map],
    dsimp [coproduct_kernel_comparison],
    simp only [category.id_comp, colimit.ι_desc_assoc, cofan.mk_ι_app, kernel.lift_ι] },
  have sqπ : π₁ ≫ Q.inv = E.inv ≫ π₂,
  { dsimp [π₁, Q, E, π₂, coproduct_kernel_comparison], apply colimit.hom_ext, rintros ⟨a⟩,
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc,
      has_colimit.iso_of_nat_iso_ι_inv_assoc, discrete.nat_iso_inv_app,
      colimit.comp_cocone_point_unique_up_to_iso_inv, functor.map_cocone_ι_app,
      colimit.cocone_ι, colimit.comp_cocone_point_unique_up_to_iso_inv_assoc,
      homological_complex.eval_map],
    dsimp,
    simp only [homological_complex.hom.comm_from, category.id_comp],
    erw category.id_comp,
    refl },
  have e1 : exact ι₁ π₁,
  { apply exact_coproduct, intros b, exact exact_kernel_ι },
  have e2 : exact ι₂ π₂ := exact_kernel_ι,
  have hι₂ := abelian.pseudoelement.pseudo_injective_of_mono ι₂,
  replace e1 := abelian.pseudoelement.pseudo_exact_of_exact e1,
  replace e2 := abelian.pseudoelement.pseudo_exact_of_exact e2,
  have hEinv := abelian.pseudoelement.pseudo_surjective_of_epi E.inv,
  have hQinv := abelian.pseudoelement.pseudo_injective_of_mono Q.inv,
  apply abelian.pseudoelement.epi_of_pseudo_surjective,
  -- Now we start the diagram chase.
  intros x,
  let x' := ι₂ x,
  obtain ⟨y,hy⟩ := hEinv x',
  have hy' : π₁ y = 0,
  { apply hQinv,
    simp only [abelian.pseudoelement.apply_zero, ← abelian.pseudoelement.comp_apply, sqπ],
    rw [abelian.pseudoelement.comp_apply, hy],
    dsimp only [x'], rw e2.1 },
  obtain ⟨z,hz⟩ := e1.2 _ hy',
  use z,
  apply hι₂,
  rw [← abelian.pseudoelement.comp_apply, ← sqι, abelian.pseudoelement.comp_apply, hz, hy],
end
end

instance is_iso_coproduct_kernel_comparison (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts.{v} A] [AB4 A] (i : M) (X : α → homological_complex A S) :
is_iso (coproduct_kernel_comparison M S α i X) :=
is_iso_of_mono_of_epi _

noncomputable
def coproduct_homology_comparison (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts.{v} A] (i : M) (X : α → homological_complex A S) :
  (∐ λ a : α, (X a).homology i) ⟶ (∐ X).homology i :=
sigma.desc $ λ b, (homology_functor _ _ _).map $ sigma.ι _ _

noncomputable
def coproduct_homology_comparison_inv (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts.{v} A] [AB4 A] (i : M) (X : α → homological_complex A S) :
  (∐ X).homology i ⟶ (∐ λ a : α, (X a).homology i) :=
homology.desc' _ _ _ (inv (coproduct_kernel_comparison M S α i X) ≫
  sigma.desc (λ b, homology.π' ((X b).d_to _) ((X b).d_from i)
    (homological_complex.d_to_comp_d_from _ _) ≫ sigma.ι _ b))
begin
  rw ← category.assoc, let t := _, change t ≫ _ = _,
  let e : (∐ X).X_prev i ≅ ∐ (λ a, (X a).X_prev i) :=
    (is_colimit_of_preserves (eval_prev A S i)
      (colimit.is_colimit _)).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫ has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ b, iso.refl _),
  have ht : t = e.hom ≫ sigma.desc (λ b, _ ≫ sigma.ι _ b),
  rotate 2,
  { refine kernel.lift _ _ _, exact (X b).d_to i,
    exact (X b).d_to_comp_d_from i },
  { dsimp [t, e, limits.is_colimit.cocone_point_unique_up_to_iso,
      has_colimit.iso_of_nat_iso, is_colimit.map, coproduct_kernel_comparison],
    rw is_iso.comp_inv_eq,
    apply (is_colimit_of_preserves (eval_prev A S i)
      (colimit.is_colimit (discrete.functor X))).hom_ext,
    rintros ⟨j⟩,
    apply equalizer.hom_ext,
    simp only [functor.map_cocone_ι_app, colimit.cocone_ι,
      equalizer_as_kernel, category.assoc, kernel.lift_ι],
    slice_rhs 1 2
    { erw (is_colimit_of_preserves (eval_prev A S i) (colimit.is_colimit (discrete.functor X))).fac },
    dsimp [eval_prev],
    simp only [homological_complex.hom.comm_to, colimit.ι_desc, cocones.precompose_obj_ι,
      nat_trans.comp_app, discrete.nat_iso_hom_app, colimit.cocone_ι, category.assoc,
      cofan.mk_ι_app, kernel.lift_ι, kernel.lift_ι_assoc],
    dsimp, simp only [category.id_comp] },
  { rw ht,
    dsimp [e, limits.is_colimit.cocone_point_unique_up_to_iso],
    apply (is_colimit_of_preserves (eval_prev A S i) (colimit.is_colimit (discrete.functor X))).hom_ext,
    intros j,
    simp only [functor.map_cocone_ι_app, colimit.cocone_ι, category.assoc,
      has_colimit.iso_of_nat_iso_hom_desc, comp_zero],
    slice_lhs 1 2
    { erw (is_colimit_of_preserves (eval_prev A S i) (colimit.is_colimit (discrete.functor X))).fac },
    simp only [colimit.cocone_ι, colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app,
      cofan.mk_ι_app, category.assoc, homology.condition_π'_assoc, zero_comp, comp_zero] }
end

noncomputable
def coproduct_homology_iso
  (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts.{v} A] [AB4 A] (i : M) (X : α → homological_complex A S) :
  (∐ λ a : α, (X a).homology i) ≅ (∐ X).homology i :=
{ hom := coproduct_homology_comparison _ _ _ _ _,
  inv := coproduct_homology_comparison_inv _ _ _ _ _,
  hom_inv_id' := begin
    dsimp [coproduct_homology_comparison, coproduct_homology_comparison_inv],
    apply colimit.hom_ext, rintros ⟨a⟩,
    dsimp,
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.comp_id],
    apply homology.hom_from_ext,
    rw homology.map_eq_desc'_lift_left,
    simp only [homological_complex.hom.sq_from_left, homology.π'_desc'_assoc],
    let t := _, change t ≫ _ = _,
    have ht : t = kernel.lift _ (kernel.ι _ ≫ _) _ ≫ homology.π' _ _ _,
    rotate 2,
    { let e : X a ⟶ ∐ X := sigma.ι _ a, exact e.f i },
    { dsimp,
      rw [category.assoc, (sigma.ι X a : X a ⟶ ∐ X).comm_from, ← category.assoc,
        kernel.condition, zero_comp] },
    { dsimp [t], apply homology.hom_to_ext,
      simp only [category.assoc, homology.lift_ι, homological_complex.homology.π'_ι,
        kernel.lift_ι_assoc] },
    { rw ht, clear ht, clear t,
      rw [category.assoc, homology.π'_desc', ← category.assoc],
      let t := _, change t ≫ _ = _,
      have ht : t = sigma.ι _ a,
      { dsimp [t], rw is_iso.comp_inv_eq,
        apply equalizer.hom_ext,
        dsimp [coproduct_kernel_comparison],
        simp only [category.assoc, kernel.lift_ι],
        erw colimit.ι_desc_assoc,
        dsimp,
        simp only [kernel.lift_ι] },
      rw ht, clear ht, clear t,
      erw colimit.ι_desc,
      refl }
  end,
  inv_hom_id' := begin
    dsimp [coproduct_homology_comparison, coproduct_homology_comparison_inv],
    apply homology.hom_from_ext,
    simp only [homology.π'_desc'_assoc, category.assoc, category.comp_id,
      is_iso.inv_comp_eq],
    apply colimit.hom_ext, rintros ⟨a⟩,
    dsimp,
    simp only [homological_complex.hom.sq_from_right, homological_complex.hom.sq_to_right,
      colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, colimit.ι_desc, homology.π'_map],
    erw colimit.ι_desc_assoc, refl,
  end }

noncomputable
def is_colimit_homology_map_cocone  (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts.{v} A] [AB4 A] (i : M) (X : α → homological_complex A S) :
  is_colimit ((homology_functor A S i).map_cocone (colimit.cocone (discrete.functor X))) :=
{ desc := λ E, (coproduct_homology_iso _ _ _ _ _).inv ≫ sigma.desc (λ a, E.ι.app ⟨_⟩),
  fac' := begin
    rintros E ⟨j⟩,
    dsimp [coproduct_homology_comparison_inv, coproduct_homology_iso],
    apply homology.hom_from_ext,
    rw homology.map_eq_desc'_lift_left,
    simp only [homological_complex.hom.sq_from_left, homology.π'_desc'_assoc],
    let t := _, change t ≫ _ = _,
    have ht : t = kernel.lift _ (kernel.ι _ ≫ _) _ ≫ homology.π' _ _ _,
    rotate 2,
    { let e := (sigma.ι X j), exact e.f i },
    { dsimp, rw [category.assoc],
      erw (sigma.ι X j : X j ⟶ ∐ X).comm_from,
      rw [← category.assoc, kernel.condition, zero_comp] },
    { dsimp [t],
      apply homology.hom_to_ext,
      simp only [category.assoc, homology.lift_ι, homological_complex.homology.π'_ι,
        kernel.lift_ι_assoc] },
    rw ht, clear ht, clear t,
    simp only [category.assoc, homology.π'_desc'_assoc],
    simp only [← category.assoc],
    let t := _, change (t ≫ _) ≫ _ = _,
    have ht : t = sigma.ι _ j,
    { dsimp [t], rw [is_iso.comp_inv_eq],
      dsimp [coproduct_kernel_comparison],
      erw colimit.ι_desc, refl },
    rw ht, clear ht, clear t,
    simp only [category.assoc], erw [colimit.ι_desc_assoc], dsimp,
    rw [category.assoc, colimit.ι_desc], refl,
  end,
  uniq' := begin
    intros E m hm,
    rw iso.eq_inv_comp, dsimp [coproduct_homology_comparison, coproduct_homology_iso],
    apply colimit.hom_ext, rintros ⟨j⟩, specialize hm ⟨j⟩,
    simpa only [←hm, colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc,
      functor.map_cocone_ι_app, colimit.cocone_ι,
      homology_functor_map],
  end }

noncomputable
instance homology_functor_preserves_coproducts
  (M : Type*) (S : complex_shape M) (α : Type v)
  [abelian A] [has_coproducts.{v} A] [AB4 A] (i) :
  preserves_colimits_of_shape (discrete α)
  (homology_functor A S i) :=
begin
  constructor, intros K,
  let E : K ≅ discrete.functor (λ n, K.obj ⟨n⟩) := discrete.nat_iso (λ ⟨i⟩, iso.refl _),
  suffices : preserves_colimit (discrete.functor (λ n, K.obj ⟨n⟩)) (homology_functor A _ i),
  { apply preserves_colimit_of_iso_diagram _ E.symm, assumption },
  apply preserves_colimit_of_preserves_colimit_cocone
    (colimit.is_colimit (discrete.functor (λ n, K.obj ⟨n⟩))),
  apply is_colimit_homology_map_cocone,
end

noncomputable
def is_colimit_homotopy_category_homology_functor_map_cocone
  {α : Type v} [abelian A] [has_coproducts.{v} A] [AB4 A] (i)
  (K : α → homotopy_category A (complex_shape.up ℤ)) :
  is_colimit
  ((homotopy_category.homology_functor A (complex_shape.up ℤ) i).map_cocone
    (homotopy_category.colimit_cofan K)) :=
{ desc := λ S,
    (is_colimit_of_preserves (homology_functor A (complex_shape.up ℤ) i)
    (colimit.is_colimit $ discrete.functor $ λ i, (K i).as)).desc ⟨S.X,
    discrete.nat_trans $ λ i, S.ι.app i⟩,
  fac' := begin
    rintros S ⟨j⟩, dsimp,
    erw (is_colimit_of_preserves (homology_functor A (complex_shape.up ℤ) i)
      (colimit.is_colimit (discrete.functor (λ (i : α), (K i).as)))).fac,
    refl,
  end,
  uniq' := begin
    intros S m hm,
    apply (is_colimit_of_preserves (homology_functor A (complex_shape.up ℤ) i)
      (colimit.is_colimit (discrete.functor (λ (i : α), (K i).as)))).hom_ext,
    rintros ⟨j⟩,
    erw (is_colimit_of_preserves (homology_functor A (complex_shape.up ℤ) i)
      (colimit.is_colimit (discrete.functor (λ (i : α), (K i).as)))).fac,
    dsimp, rw ← hm, refl,
  end }

noncomputable
instance homotopy_category_homology_functor_preserves_coproducts
  (α : Type v)
  [abelian A] [has_coproducts.{v} A] [AB4 A] (i) :
  preserves_colimits_of_shape (discrete α)
  (homotopy_category.homology_functor A (complex_shape.up ℤ) i) :=
begin
  constructor, intros K,
  let E : K ≅ discrete.functor (λ n, K.obj ⟨n⟩) := discrete.nat_iso (λ ⟨i⟩, iso.refl _),
  suffices : preserves_colimit (discrete.functor (λ n, K.obj ⟨n⟩))
    (homotopy_category.homology_functor A _ i),
  { apply preserves_colimit_of_iso_diagram _ E.symm, assumption },
  apply preserves_colimit_of_preserves_colimit_cocone
    (homotopy_category.is_colimit_cofan (λ n, K.obj ⟨n⟩)),
  apply is_colimit_homotopy_category_homology_functor_map_cocone,
end

end category_theory
