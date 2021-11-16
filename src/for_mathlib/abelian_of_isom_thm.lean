import category_theory.abelian.basic
import category_theory.additive.basic
import algebra.homology.exact

namespace category_theory
open category_theory.limits

noncomputable
example (A : Type*) [category A] [abelian A] : has_zero_object A := by apply_instance

variables {C : Type*} [category C] [additive_category C] [has_kernels C] [has_cokernels C]

noncomputable theory

abbreviation coim {X Y : C} (f : X ⟶ Y) := cokernel (kernel.ι f)
abbreviation im {X Y : C} (f : X ⟶ Y) := kernel (cokernel.π f)

@[simps]
def im_mono_factorisation {X Y : C} (f : X ⟶ Y) : mono_factorisation f :=
{ I := im f,
  m := kernel.ι _,
  m_mono := infer_instance,
  e := kernel.lift _ f (cokernel.condition _),
  fac' := kernel.lift_ι _ _ _ }

-- move this
@[simp] lemma limits.mono_factorisation.kernel_ι_comp {X Y : C} {f : X ⟶ Y}
  (F : mono_factorisation f) :
  kernel.ι f ≫ F.e = 0 :=
by rw [← cancel_mono F.m, zero_comp, category.assoc, F.fac, kernel.condition]

def coim_to_im {X Y : C} (f : X ⟶ Y) : coim f ⟶ im f :=
cokernel.desc _ (im_mono_factorisation f).e $ (im_mono_factorisation f).kernel_ι_comp

def im_image_factorisation {X Y : C} (f : X ⟶ Y) [is_iso (coim_to_im f)] :
  image_factorisation f :=
{ F := im_mono_factorisation f,
  is_image :=
  { lift := λ F, inv (coim_to_im f) ≫ cokernel.desc _ F.e F.kernel_ι_comp,
    lift_fac' := λ F, begin
      simp only [im_mono_factorisation_m, is_iso.inv_comp_eq, category.assoc, coim_to_im],
      ext,
      erw [limits.coequalizer.π_desc_assoc, limits.coequalizer.π_desc_assoc, F.fac,
        (im_mono_factorisation f).fac],
    end } }
.

lemma im_mono_factorisaction.e_eq {X Y : C} (f : X ⟶ Y) :
  (im_mono_factorisation f).e = cokernel.π _ ≫ coim_to_im f :=
by { ext, simp only [coim_to_im, im_mono_factorisation_e, category.assoc, cokernel.π_desc_assoc] }

-- def im_strong_epi_mono_factorisation {X Y : C} (f : X ⟶ Y) [is_iso (coim_to_im f)] :
--   strong_epi_mono_factorisation f :=
-- { e_strong_epi :=
--   { epi := by { dsimp only, rw im_mono_factorisaction.e_eq, exact epi_comp _ _ },
--     has_lift := λ X' Y' g h m hm H, begin
--       constructor, constructor, dsimp only [im_mono_factorisation] at h H ⊢, resetI,
--       refine
--       { lift := _,
--         fac_left' := _,
--         fac_right' := _ },
--       { refine inv (coim_to_im f) ≫ _, dsimp,  }
--     end },
--   .. im_mono_factorisation f }

lemma has_images_of_has_kernels_of_has_cokernels
  (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), is_iso (coim_to_im f)) : has_images C :=
{ has_image := λ X Y f,
  { exists_image := ⟨im_image_factorisation f⟩ } }

def has_zero_object_of_isom_thm [H : nonempty C]
  (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), is_iso (coim_to_im f)) : has_zero_object C :=
{ zero := im (0 : H.some ⟶ H.some),
  unique_to := λ X, ⟨⟨0⟩, λ f, begin
    rw ← cancel_epi (coim_to_im _), swap, { apply_instance },
    ext,
    rw ← cancel_epi (kernel.ι (0 : H.some ⟶ H.some)),
    simp only [coim_to_im, category.assoc, coequalizer.condition_assoc, zero_comp],
  end⟩,
  unique_from := λ X, ⟨⟨0⟩, λ f, begin
    ext,
    rw ← cancel_mono (cokernel.π (0 : H.some ⟶ H.some)),
    simp only [category.assoc, equalizer.condition, comp_zero],
  end⟩ }
.

-- move this
def _root_.fin.elim {α : Sort*} (x : fin 0) : α := x.elim0

def has_zero_object_of_has_finite_biproducts
  (D : Type*) [category D] [has_zero_morphisms D] [has_finite_biproducts D] :
  has_zero_object D :=
{ zero := biproduct (λ i : ulift (fin 0), i.down.elim),
  unique_to := λ X, ⟨⟨0⟩, λ f, by { ext i, exact i.down.elim }⟩,
  unique_from := λ X, ⟨⟨0⟩, λ f, by { ext i, exact i.down.elim }⟩, }

instance (D : Type*) [category D] [has_zero_morphisms D] [has_finite_biproducts D] : nonempty D :=
⟨biproduct (λ i : ulift (fin 0), i.down.elim)⟩

instance iso_im_of_mono [has_images C] [has_equalizers C] [has_zero_object C]
  {X Y : C} (f : X ⟶ Y) [mono f] [is_iso (coim_to_im f)] :
  is_iso (im_mono_factorisation f).e :=
by { rw im_mono_factorisaction.e_eq, exact is_iso.comp_is_iso }

lemma normal_mono_of_mono {X Y : C} (f : X ⟶ Y) [mono f]
  (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), is_iso (coim_to_im f)) :
  normal_mono f :=
{ Z := cokernel f,
  g := cokernel.π _,
  w := cokernel.condition _,
  is_limit := begin
    haveI : has_images C := has_images_of_has_kernels_of_has_cokernels h,
    haveI : has_equalizers C := preadditive.has_equalizers_of_has_kernels,
    letI : has_zero_object C := has_zero_object_of_has_finite_biproducts _,
    have aux : _ := _,
    refine is_limit_aux _ (λ A, limit.lift _ _ ≫ inv (im_mono_factorisation f).e) aux _,
    { intros A g hg,
      rw [kernel_fork.ι_of_ι] at hg,
      rw [← cancel_mono f, hg, ← aux, kernel_fork.ι_of_ι], },
    { intro A,
      simp only [kernel_fork.ι_of_ι, category.assoc],
      convert limit.lift_π _ _ using 2,
      rw [is_iso.inv_comp_eq, eq_comm],
      exact (im_mono_factorisation f).fac, }
  end }

instance iso_im_of_epi [has_images C] [has_equalizers C] [has_zero_object C]
  {X Y : C} (f : X ⟶ Y) [epi f] [is_iso (coim_to_im f)] :
  is_iso (im_mono_factorisation f).m :=
by { dsimp, apply_instance }

lemma normal_epi_of_epi {X Y : C} (f : X ⟶ Y) [epi f]
  (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), is_iso (coim_to_im f)) :
  normal_epi f :=
{ W := kernel f,
  g := kernel.ι _,
  w := kernel.condition _,
  is_colimit := begin
    haveI : has_images C := has_images_of_has_kernels_of_has_cokernels h,
    haveI : has_equalizers C := preadditive.has_equalizers_of_has_kernels,
    letI : has_zero_object C := has_zero_object_of_has_finite_biproducts _,
    have aux : _ := _,
    refine is_colimit_aux _
      (λ A, inv (im_mono_factorisation f).m ≫ inv (coim_to_im f) ≫ colimit.desc _ _) aux _,
    { intros A g hg,
      rw [cokernel_cofork.π_of_π] at hg,
      rw [← cancel_epi f, hg, ← aux, cokernel_cofork.π_of_π], },
    { intro A,
      simp only [cokernel_cofork.π_of_π, ← category.assoc],
      convert colimit.ι_desc _ _ using 2,
      rw [is_iso.comp_inv_eq, is_iso.comp_inv_eq, eq_comm, ← im_mono_factorisaction.e_eq],
      exact (im_mono_factorisation f).fac, }
  end }

def abelian_of_coim_to_im (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), is_iso (coim_to_im f)) :
  abelian C :=
{ normal_mono := λ X Y f hf, by exactI normal_mono_of_mono f h,
  normal_epi := λ X Y f hf, by exactI normal_epi_of_epi f h, }

end category_theory
