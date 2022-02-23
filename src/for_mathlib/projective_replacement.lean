import category_theory.abelian.projective
import for_mathlib.homological_complex_shift
import tactic.linarith
import algebra.homology.quasi_iso
import category_theory.abelian.diagram_lemmas.four

.

open category_theory category_theory.limits

open_locale zero_object

section zero_object

variables {V : Type*} [category V] [has_zero_object V] [has_zero_morphisms V]

def is_zero_object (X : V) := is_iso (0 : X ⟶ 0)

lemma is_zero_object_iff_eq {X : V} : is_zero_object X ↔ 𝟙 X = 0 :=
begin
  split,
  { rintro (h : is_iso _),
    resetI,
    rw ← cancel_mono (0 : X ⟶ 0),
    simp },
  { intro e,
    use 0,
    rw e,
    split; simp }
end

lemma is_zero_object.to_eq_zero {X Y : V} (h : is_zero_object Y) (f : X ⟶ Y) : f = 0 :=
begin
  rw [← cancel_mono (𝟙 _), (is_zero_object_iff_eq.mp h), comp_zero, comp_zero],
  apply_instance
end

lemma is_zero_object.from_eq_zero {X Y : V} (h : is_zero_object X) (f : X ⟶ Y) : f = 0 :=
begin
  rw [← cancel_epi (𝟙 _), is_zero_object_iff_eq.mp h, zero_comp, comp_zero],
  apply_instance
end

lemma is_zero_object_of_mono {X Y : V} (f : X ⟶ Y) [mono f] (h : is_zero_object Y) :
  is_zero_object X :=
by rw [is_zero_object_iff_eq, ← cancel_mono f, zero_comp, h.to_eq_zero (𝟙 _ ≫ f)]

lemma is_zero_object_of_epi {X Y : V} (f : X ⟶ Y) [epi f] (h : is_zero_object X) :
  is_zero_object Y :=
by rw [is_zero_object_iff_eq, ← cancel_epi f, comp_zero, h.from_eq_zero (f ≫ 𝟙 Y)]

lemma zero_is_zero_object : is_zero_object (0 : V) :=
by { rw is_zero_object_iff_eq, simp }

lemma split_epi_of_is_zero_object {X Y : V} (f : X ⟶ Y) (h : is_zero_object Y) : split_epi f :=
⟨0, by simp [is_zero_object_iff_eq.mp h]⟩

lemma epi_of_is_zero_object {X Y : V} (f : X ⟶ Y) (h : is_zero_object Y) : epi f :=
@@split_epi.epi _ _ (split_epi_of_is_zero_object f h)

lemma split_mono_of_is_zero_object {X Y : V} (f : X ⟶ Y) (h : is_zero_object X) : split_mono f :=
⟨0, by simp [is_zero_object_iff_eq.mp h]⟩

lemma mono_of_is_zero_object {X Y : V} (f : X ⟶ Y) (h : is_zero_object X) : mono f :=
@@split_mono.mono _ _ (split_mono_of_is_zero_object f h)

lemma is_iso_of_is_zero_object {X Y : V} (f : X ⟶ Y)
  (h₁ : is_zero_object X) (h₂ : is_zero_object Y) : is_iso f :=
begin
  use 0,
  rw [is_zero_object_iff_eq.mp h₁, is_zero_object_iff_eq.mp h₂],
  split; simp
end

end zero_object

variables {V : Type*} [category V] [abelian V] [enough_projectives V] (X : cochain_complex V ℤ)
variables (a : ℤ) (H : ∀ i (h : a ≤ i), is_zero_object (X.X i))

lemma comp_eq_to_hom_heq_iff {C : Type*} [category C] {X X' Y Y' Y'' : C}
  (f : X ⟶ Y) (f' : X' ⟶ Y') (e : Y = Y'') : f ≫ eq_to_hom e == f' ↔ f == f' :=
by { subst e, erw category.comp_id }

lemma eq_to_hom_comp_heq_iff {C : Type*} [category C] {X X' Y Y' X'' : C}
  (f : X ⟶ Y) (f' : X' ⟶ Y') (e : X'' = X) : eq_to_hom e ≫ f == f' ↔ f == f' :=
by { subst e, erw category.id_comp }

lemma heq_eq_to_hom_comp_iff {C : Type*} [category C] {X X' Y Y' X'' : C}
  (f : X ⟶ Y) (f' : X' ⟶ Y') (e : X'' = X') : f == eq_to_hom e ≫ f' ↔ f == f' :=
by { subst e, erw category.id_comp }

lemma heq_comp_eq_to_hom_iff {C : Type*} [category C] {X X' Y Y' Y'' : C}
  (f : X ⟶ Y) (f' : X' ⟶ Y') (e : Y' = Y'') : f == f' ≫ eq_to_hom e ↔ f == f' :=
by { subst e, erw category.comp_id }

include H

namespace category_theory.projective

noncomputable
def replacement_aux : Π n : ℕ, Σ f : arrow V, (f.left ⟶ X.X (a-n))
| 0 := ⟨⟨0, 0, 0⟩, 0⟩
| (n+1) := ⟨⟨over
    (pullback (X.d (a-n-1) (a-n)) (kernel.ι (replacement_aux n).1.hom ≫ (replacement_aux n).2)),
  (replacement_aux n).1.left, π _ ≫ pullback.snd ≫ kernel.ι _⟩,
  π _ ≫ pullback.fst ≫ (X.X_eq_to_iso (by { norm_num, exact sub_sub _ _ _ })).hom⟩
.

lemma replacement_aux_right_eq (n : ℕ) :
  (replacement_aux X a H (n + 1)).1.right = (replacement_aux X a H n).1.left :=
by { delta replacement_aux, exact rfl }

lemma replacement_aux_hom_eq (n : ℕ) :
  (replacement_aux X a H (n + 1)).1.hom = eq_to_hom (by { delta replacement_aux, exact rfl }) ≫
    π (pullback (X.d (a-n-1) (a-n)) (kernel.ι
      (replacement_aux X a H n).1.hom ≫ (replacement_aux X a H n).2)) ≫
    pullback.snd ≫ kernel.ι (replacement_aux X a H n).1.hom ≫
    eq_to_hom (by { delta replacement_aux, exact rfl }) :=
by { delta replacement_aux, erw [category.id_comp, category.comp_id], exact rfl }
.

lemma replacement_aux_snd_comm (n : ℕ) :
  (replacement_aux X a H (n + 1)).1.hom ≫ eq_to_hom (replacement_aux_right_eq X a H n) ≫
    (replacement_aux X a H n).2 = (replacement_aux X a H (n + 1)).2 ≫ X.d _ _ :=
begin
  rw replacement_aux_hom_eq,
  simp only [category.id_comp, eq_to_hom_refl, category.assoc, eq_to_hom_trans_assoc],
  delta replacement_aux,
  rw [eq_to_hom_refl, category.id_comp, ← pullback.condition],
  erw [category.assoc, category.assoc, homological_complex.X_eq_to_iso_d],
end

noncomputable
def replacement : cochain_complex V ℤ :=
{ X := λ i, if a < i then 0 else (replacement_aux X a H ((a - i).nat_abs + 1)).1.right,
  d := λ i j, if h₁ : i + 1 = j then if h₂ : j > a then 0 else
      eq_to_hom (begin
        rw [if_neg, replacement_aux_right_eq, functor.id_obj],
        subst h₁,
        suffices : (a - i).nat_abs = (a - (i + 1)).nat_abs + 1,
        { rw this },
        apply int.coe_nat_inj,
        norm_num [← int.abs_eq_nat_abs],
        rw [abs_eq_self.mpr _, abs_eq_self.mpr _],
        all_goals { linarith }
      end) ≫
      (replacement_aux X a H ((a - j).nat_abs + 1)).fst.hom ≫ eq_to_hom (dif_neg h₂).symm else 0,
  shape' := λ _ _ e, dif_neg e,
  d_comp_d' := begin
    rintros i j k (rfl : i+1 = j) (rfl : i+1+1 = k),
    simp only [dif_pos, dif_ctx_congr],
    by_cases h : i + 1 + 1 > a,
    { rw [dif_pos h, comp_zero] },
    rw [dif_neg h, dif_neg],
    rw [← category.assoc, ← category.assoc, ← is_iso.eq_comp_inv],
    simp only [category.assoc, eq_to_hom_trans_assoc],
    rw [← is_iso.eq_inv_comp, zero_comp, comp_zero, replacement_aux_hom_eq],
    simp only [category.assoc, eq_to_hom_trans_assoc],
    iterate 3 { convert comp_zero },
    suffices : (a - (i + 1)).nat_abs = (a - (i + 1 + 1)).nat_abs + 1,
    { convert kernel.condition _; try { rw this }, apply (eq_to_hom_comp_heq_iff _ _ _).mpr,
      congr; rw this },
    apply int.coe_nat_inj,
    norm_num [← int.abs_eq_nat_abs],
    rw [abs_eq_self.mpr _, abs_eq_self.mpr _],
    all_goals { linarith }
  end }

noncomputable
def replacement.hom : replacement X a H ⟶ X :=
{ f := λ i, if h : a < i then 0 else eq_to_hom (if_neg h) ≫
    eq_to_hom (by rw replacement_aux_right_eq) ≫
    (replacement_aux X a H ((a - i).nat_abs)).snd ≫
    (X.X_eq_to_iso (by { rw [← int.abs_eq_nat_abs, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add',
      eq_comm, abs_eq_self], linarith })).hom,
  comm' := begin
    rintros i j (rfl : i+1 = j),
    split_ifs with h',
    { rw [zero_comp, comp_zero] },
    { exfalso, linarith },
    { haveI : is_iso (0 : X.X (i + 1) ⟶ 0) := H _ (le_of_lt h),
      rw [← cancel_mono (0 : X.X (i + 1) ⟶ 0), comp_zero, comp_zero] },
    { dsimp only [replacement],
      rw [dif_pos rfl, dif_neg h],
      simp only [← category.assoc, eq_to_hom_trans_assoc],
      rw [← is_iso.comp_inv_eq],
      simp only [homological_complex.X_d_eq_to_iso, homological_complex.X_eq_to_iso_inv,
        category.assoc, homological_complex.X_eq_to_iso_d, eq_to_hom_trans, is_iso.iso.inv_hom],
      rw [← is_iso.inv_comp_eq, inv_eq_to_hom, eq_to_hom_trans_assoc],
      refine eq.trans _ (replacement_aux_snd_comm X a H _).symm,
      suffices : (a - (i + 1)).nat_abs + 1 = (a - i).nat_abs,
      { rw ← heq_iff_eq, apply (eq_to_hom_comp_heq_iff _ _ _).mpr, rw this },
      apply int.coe_nat_inj,
      norm_num [← int.abs_eq_nat_abs],
      rw [abs_eq_self.mpr _, abs_eq_self.mpr _],
      all_goals { linarith } }
  end }
.
noncomputable
def replacement_nat : chain_complex V ℕ :=
{ X := λ i, (replacement_aux X a H i).1.right,
  d := λ i j, if h₁ : j + 1 = i then eq_to_hom (by { subst h₁, dsimp [replacement_aux], refl }) ≫
    (replacement_aux X a H _).fst.hom else 0,
  shape' := λ _ _ e, dif_neg e,
  d_comp_d' := begin
    rintros i j k (rfl : j+1 = i) (rfl : k+1 = j),
    simp [replacement_aux_hom_eq]
  end }

omit H
variables {V} {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
variables {A' B' C' : V} {f' : A' ⟶ B'} {g' : B' ⟶ C'} (w' : f' ≫ g' = 0)
variables (α : arrow.mk f ⟶ arrow.mk f') (β : arrow.mk g ⟶ arrow.mk g')
variables (p : α.right = β.left)

instance : epi (homology.π f g w) :=
by { delta homology.π, apply_instance }

instance : strong_epi (factor_thru_image f) :=
strong_epi_factor_thru_image_of_strong_epi_mono_factorisation $
      classical.choice $ has_strong_epi_mono_factorisations.has_fac f

instance : epi (factor_thru_image f ≫ (image_subobject_iso f).inv) :=
epi_comp _ _

noncomputable
def cokernel_lift_to_kernel_desc :
  cokernel (kernel.lift g f w) ⟶ kernel (cokernel.desc f g w) :=
cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ cokernel.π _) (by simp)) (by { ext, simp })
.
open_locale pseudoelement
open category_theory.abelian

lemma exists_preimage_of_cokernel_π (x : B) (e : cokernel.π f x = 0) : ∃ (y : A), f y = x :=
(@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _(exact_cokernel _)).2 _ e

instance : mono (cokernel_lift_to_kernel_desc f g w) :=
begin
  apply_with (mono_of_mono _ (kernel.ι _)) { instances := ff },
  apply pseudoelement.mono_of_zero_of_map_zero,
  intros x hx,
  obtain ⟨x', rfl⟩ := abelian.pseudoelement.pseudo_surjective_of_epi (cokernel.π _) x,
  replace hx : cokernel.π f (kernel.ι g x') = 0,
  { simpa [← pseudoelement.comp_apply, cokernel_lift_to_kernel_desc] using hx },
  obtain ⟨y, hy⟩ := exists_preimage_of_cokernel_π _ _ hx,
  rw [(kernel.lift_ι g f w).symm, pseudoelement.comp_apply] at hy,
  replace hy := pseudoelement.pseudo_injective_of_mono _ hy,
  subst hy,
  simp [← pseudoelement.comp_apply]
end
.
instance : epi (cokernel_lift_to_kernel_desc f g w) :=
begin
  apply_with (epi_of_epi (cokernel.π _)) { instances := ff },
  apply pseudoelement.epi_of_pseudo_surjective,
  intro x,
  obtain ⟨x', hx'⟩ := abelian.pseudoelement.pseudo_surjective_of_epi (cokernel.π _)
    (kernel.ι (cokernel.desc f g w) x),
  have hx : g x' = 0,
  { simpa [← pseudoelement.comp_apply] using congr_arg (cokernel.desc f g w) hx' },
  obtain ⟨y, rfl⟩ := (@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ exact_kernel_ι).2 x' hx,
  use y,
  apply pseudoelement.pseudo_injective_of_mono (kernel.ι (cokernel.desc f g w)),
  simpa [← pseudoelement.comp_apply, cokernel_lift_to_kernel_desc] using hx',
end

instance : is_iso (cokernel_lift_to_kernel_desc f g w) :=
is_iso_of_mono_of_epi _

noncomputable
def cokernel_lift_iso_kernel_desc : cokernel (kernel.lift g f w) ≅ kernel (cokernel.desc f g w) :=
as_iso (cokernel_lift_to_kernel_desc f g w)

noncomputable
def homology.to_cokernel :
  homology f g w ⟶ cokernel f :=
(homology_iso_cokernel_lift f g w).hom ≫ (cokernel_lift_iso_kernel_desc f g w).hom ≫ kernel.ι _

instance : mono (homology.to_cokernel f g w) :=
by { delta homology.to_cokernel, apply_instance }

@[simp, reassoc]
lemma π_cokernel_iso_of_eq {f₁ f₂ : A ⟶ B} (e : f₁ = f₂) :
  cokernel.π f₁ ≫ (cokernel_iso_of_eq e).hom = cokernel.π f₂ :=
by { subst e, erw has_colimit.iso_of_nat_iso_ι_hom, exact category.id_comp _ }

@[simp, reassoc]
lemma homology.π_iso_cokernel_lift_hom :
  homology.π f g w ≫ (homology_iso_cokernel_lift f g w).hom =
    (kernel_subobject_iso _).hom ≫ cokernel.π _ :=
begin
  simp only [limits.cokernel_epi_comp_inv, iso.symm_hom, homology_iso_cokernel_lift,
    iso.trans_hom],
  erw homology.π_desc_assoc,
  simp only [cokernel.π_desc_assoc, category.assoc, iso.cancel_iso_hom_left,
    π_cokernel_iso_of_eq],
end

@[simp, reassoc]
lemma homology.π_to_cokernel :
  homology.π f g w ≫ homology.to_cokernel f g w = (kernel_subobject _).arrow ≫ cokernel.π _ :=
begin
  delta homology.to_cokernel cokernel_lift_iso_kernel_desc cokernel_lift_to_kernel_desc,
  simp,
end


open_locale pseudoelement
open category_theory.abelian

lemma mono_homology_map_of_pseudoelement
  (H : ∀ (x : B) (y : A') (h₁ : g x = 0) (h₂ : f' y = α.right x), ∃ z : A, f z = x) :
  mono (homology.map w w' α β p) :=
begin
  apply pseudoelement.mono_of_zero_of_map_zero,
  intros x e,
  obtain ⟨x', rfl⟩ := pseudoelement.pseudo_surjective_of_epi (homology.π f g w) x,
  rw [← pseudoelement.comp_apply, homology.π_map, pseudoelement.comp_apply] at e,
  obtain ⟨y, hy⟩ := (@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _
    (homology.π f' g' w') (exact_cokernel _)).2 _ e,
  obtain ⟨y', rfl⟩ := pseudoelement.pseudo_surjective_of_epi
    (factor_thru_image f' ≫ (image_subobject_iso _).inv) y,
  obtain ⟨z, e'⟩ := H ((kernel_subobject g).arrow x') y'
    (by rw [← pseudoelement.comp_apply, kernel_subobject_arrow_comp, pseudoelement.zero_apply])
    (by simpa [← pseudoelement.comp_apply, p] using congr_arg (kernel_subobject g').arrow hy),
  have : f = (factor_thru_image f ≫ (image_subobject_iso _).inv ≫ image_to_kernel f g w) ≫
    (kernel_subobject g).arrow := by simp,
  rw [this, pseudoelement.comp_apply] at e',
  have := pseudoelement.pseudo_injective_of_mono _ e', subst this,
  simp [← pseudoelement.comp_apply]
end
.
lemma mono_homology_map_of_epi_pullback_lift
  (H : epi (pullback.lift _ _
    (show α.left ≫ f' = (kernel.lift g f w) ≫ kernel.ι _ ≫ α.right, by simp))) :
  mono (homology.map w w' α β p) :=
begin
  apply mono_homology_map_of_pseudoelement,
  intros x y e₁ e₂,
  obtain ⟨x', rfl⟩ := (@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ exact_kernel_ι).2 x e₁,
  rw ← pseudoelement.comp_apply at e₂,
  obtain ⟨z, rfl, rfl⟩ := pseudoelement.pseudo_pullback e₂,
  obtain ⟨z', rfl⟩ := @@pseudoelement.pseudo_surjective_of_epi _ _ _ H z,
  use z',
  simp [← pseudoelement.comp_apply]
end
.

lemma epi_homology_map_of_pseudoelement
  (H : ∀ (x : B') (h : g' x = 0),
    ∃ (y : B), g y = 0 ∧ (cokernel.π f') (α.right y) = cokernel.π f' x) :
  epi (homology.map w w' α β p) :=
begin
  apply pseudoelement.epi_of_pseudo_surjective,
  intro x,
  obtain ⟨x', rfl⟩ := pseudoelement.pseudo_surjective_of_epi (homology.π f' g' w') x,
  obtain ⟨y, e₁, e₂⟩ := H ((kernel_subobject g').arrow x')
    (by rw [← pseudoelement.comp_apply, kernel_subobject_arrow_comp, pseudoelement.zero_apply]),
  obtain ⟨y', rfl⟩ := (@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _
    exact_kernel_subobject_arrow).2 y e₁,
  use homology.π f g w y',
  apply pseudoelement.pseudo_injective_of_mono (homology.to_cokernel f' g' w'),
  simpa [← pseudoelement.comp_apply, p] using e₂,
end

-- instance [H : epi (kernel.lift g' (kernel.ι g ≫ β.left)
--     (by { rw category.assoc, erw [β.w, kernel.condition_assoc], rw zero_comp }))]
--     (p : α.right = β.left) :
--   mono (homology.map w w' α β p) :=
-- begin
--   have := @abelian.mono_of_epi_of_mono_of_mono _ _ _ _ _ _ _ _ _ _ _
--     (kernel.lift _ _ w) (cokernel.π _ ≫ (homology_iso_cokernel_lift f g w).inv) (0 : _ ⟶ 0)
--     (kernel.lift _ _ w') (cokernel.π _ ≫ (homology_iso_cokernel_lift _ _ w').inv) (0 : _ ⟶ 0)
--     α.left _ _ 0 _ _ _ (show _, from _) (show _, from _) (show _, from _),
--   fapply abelian.mono_of_epi_of_mono_of_mono _ _ _ H,
--   swap 19,
--   apply abelian.exact_cokernel,
--   swap 6,
--   exact kernel.ι _,
--   swap 6,
--   exact kernel.ι _,
--   -- have := mono_of_mono_fac (homology.map_desc w w' α β p),
-- end
.

local attribute [instance] epi_comp mono_comp

noncomputable
def pullback_comp_mono_iso {X Y Z Z' : V} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ Z') [mono h] :
  pullback (f ≫ h) (g ≫ h) ≅ pullback f g :=
limit.iso_limit_cone ⟨_, pullback_is_pullback_of_comp_mono f g h⟩

@[simp, reassoc]
lemma pullback_comp_mono_iso_fst {X Y Z Z' : V} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ Z') [mono h] :
  (pullback_comp_mono_iso f g h).hom ≫ pullback.fst = pullback.fst :=
limit.iso_limit_cone_hom_π _ walking_cospan.left

lemma kernel_ι_replacement_aux_eq_zero (i : ℕ) :
  kernel.ι (replacement_aux X a H i).fst.hom ≫ (replacement_aux X a H i).snd ≫
    X.d (a - i) (a - i + 1) = 0 :=
begin
  cases i,
  { dsimp [replacement_aux], rw ← @@cancel_mono _ _ (@@is_iso.mono_of_iso _ _ (H _ _)),
    { simp }, { linarith } },
  { have : a - i.succ + 1 = a - i, { norm_num [sub_add] },
    rw [this, ← replacement_aux_snd_comm, kernel.condition_assoc, zero_comp] }
end

instance replacement_kernel_map_epi (i : ℕ) : epi (kernel.lift (X.d (a - i) (a - i + 1))
    (kernel.ι (replacement_aux X a H i).fst.hom ≫ (replacement_aux X a H i).snd)
    (by rw [category.assoc, kernel_ι_replacement_aux_eq_zero])) :=
begin
  cases i,
  { apply epi_of_is_zero_object,
    apply is_zero_object_of_mono (kernel.ι _),
    { apply H, simp },
    apply_instance },
  { apply pseudoelement.epi_of_pseudo_surjective,
    intro x,
    obtain ⟨y, h₁, h₂⟩ := @pseudoelement.pseudo_pullback _ _ _ _ _ _ _ (X.d (a - i - 1) (a - i))
      (kernel.ι (replacement_aux X a H i).fst.hom ≫ (replacement_aux X a H i).snd)
      ((X.X_eq_to_iso (by norm_num [sub_sub])).hom (kernel.ι (X.d _ _) x)) 0 _,
    swap,
    { simp only [← pseudoelement.comp_apply, category.assoc,
        homological_complex.X_eq_to_iso_d, pseudoelement.apply_zero],
      convert pseudoelement.zero_apply _ _,
      have : a - ↑i = a - ↑(i + 1) + 1 := by norm_num [← sub_sub],
      convert kernel.condition _ },
    obtain ⟨z, rfl⟩ := pseudoelement.pseudo_surjective_of_epi (projective.π _) y,
    apply_fun kernel.ι (replacement_aux X a H i).fst.hom at h₂,
    simp only [← pseudoelement.comp_apply, category.assoc, pseudoelement.apply_zero] at h₂,
    obtain ⟨w, rfl⟩ := (@pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _
      exact_kernel_ι).2 z h₂,
    dsimp [replacement_aux],
    use w,
    simp only [← pseudoelement.comp_apply] at h₁,
    apply pseudoelement.pseudo_injective_of_mono (kernel.ι (X.d (a - ↑(i + 1))
      (a - ↑(i + 1) + 1)) ≫ (homological_complex.X_eq_to_iso X _).hom),
    refine eq.trans _ h₁,
    simp only [← pseudoelement.comp_apply, category.assoc],
    congr' 1,
    refine (kernel.lift_ι_assoc _ _ _ _).trans _,
    simpa,
    apply_instance }
end

instance (i : ℕ) : epi (replacement_aux X a H i).snd :=
begin
  cases i; dsimp [replacement_aux],
  { apply epi_of_is_zero_object, apply H, simp },
  { apply_with epi_comp { instances := ff },
    { apply_instance },
    apply_with epi_comp { instances := ff },
    swap, { apply_instance },
    let e : pullback (X.d (a - i - 1) (a - i))
      (kernel.ι (replacement_aux X a H i).fst.hom ≫ (replacement_aux X a H i).snd) ≅
        pullback (kernel.lift (X.d (a - i) (a - i + 1)) _ _) (kernel.lift _ _ _),
    { refine pullback.congr_hom (kernel.lift_ι _ _ (X.d_comp_d _ _ _)).symm
        (kernel.lift_ι _ _ _).symm ≪≫ pullback_comp_mono_iso _ _ (kernel.ι _),
      rw [category.assoc, kernel_ι_replacement_aux_eq_zero] },
    have : e.hom ≫ pullback.fst = pullback.fst,
    { simp },
    refine (eq_iff_iff.mp (congr_arg epi this)).mp _,
    apply_instance },
end
-- example (n : ℤ) : n - 1 + 1 = n := by library_search

noncomputable
def homology_functor_obj_iso (X) (i : ℤ) :
  (homology_functor V (complex_shape.up ℤ) i).obj X ≅ homology _ _ (X.d_comp_d (i-1) i (i+1)) :=
homology.map_iso _ _
  (arrow.iso_mk (X.X_prev_iso (sub_add_cancel _ _)) (iso.refl _) (by { dsimp, simp [← X.d_to_eq] }))
  (arrow.iso_mk (iso.refl _) (X.X_next_iso rfl) (by { dsimp, simp })) (by { dsimp, simp})

lemma homology_functor_map_iso {X Y : cochain_complex V ℤ} (f : X ⟶ Y) (i : ℤ) :
  (homology_functor V (complex_shape.up ℤ) i).map f =
    (homology_functor_obj_iso X i).hom ≫
    homology.map _ _ (arrow.hom_mk (f.comm _ _)) (arrow.hom_mk (f.comm _ _)) rfl ≫
    (homology_functor_obj_iso Y i).inv :=
begin
  delta homology_functor_obj_iso homology.map_iso,
  simp only [homology_functor_map, homology.map_comp],
  congr; ext; dsimp,
  { delta homological_complex.hom.prev, rw (complex_shape.up ℤ).prev_eq_some (sub_add_cancel _ _) },
  { simp },
  { simp },
  { delta homological_complex.hom.next, rw (complex_shape.up ℤ).next_eq_some rfl },
end

lemma mono_homology_functor_of_pseudoelement (i : ℤ) {X Y : cochain_complex V ℤ} (f : X ⟶ Y)
  (H : ∀ (x : X.X i) (y : Y.X (i - 1)), X.d i (i + 1) x = 0 → Y.d (i - 1) i y = f.f i x →
    (∃ (z : X.X (i - 1)), X.d (i - 1) i z = x)) :
  mono ((homology_functor V (complex_shape.up ℤ) i).map f) :=
begin
  haveI := mono_homology_map_of_pseudoelement _ _ (X.d_comp_d (i-1) i (i+1))
    (Y.d_comp_d (i-1) i (i+1)) (arrow.hom_mk (f.comm _ _)) (arrow.hom_mk (f.comm _ _)) rfl H,
  rw homology_functor_map_iso,
  apply_instance
end

local attribute [instance] pseudoelement.setoid

lemma pseudoelement.id_apply {X : V} (x : X) : @@coe_fn _ pseudoelement.hom_to_fun (𝟙 X) x = x :=
begin
  apply quot.induction_on x,
  intro a,
  change ⟦over.mk _⟧ = ⟦a⟧,
  erw category.comp_id,
  rcases a with ⟨_, ⟨⟩, _⟩,
  congr,
end
.

-- def replacement_zero : (replacement X a H).X a = projective.over (X.X a) :=
-- by { dsimp [replacement], rw [if_neg (irrefl _), sub_self, int.nat_abs_zero],
--   dsimp [replacement_aux], refl, apply_instance }

def replacement_pos (i : ℤ) (e : a < i) : (replacement X a H).X i = 0 :=
if_pos e

lemma replacement_aux_comp_eq_zero (i : ℕ) :
  (replacement_aux X a H (i+1)).fst.hom ≫ eq_to_hom (by { dsimp [replacement_aux], refl }) ≫
  (replacement_aux X a H i).fst.hom = 0 :=
begin
  dsimp [replacement_aux],
  simp only [category.assoc, category.id_comp],
  refine (category.assoc _ _ _).symm.trans (eq.trans _ comp_zero),
  swap 3,
  congr' 1,
  exact kernel.condition (replacement_aux X a H i).fst.hom,
end

noncomputable
def replacement_homology_map (i : ℕ) :
  homology _ _ ((category.assoc _ _ _).trans (replacement_aux_comp_eq_zero X a H (i+1))) ⟶
  homology _ _ (X.d_comp_d (a-(i+1 : ℕ) - 1) (a-(i+1 : ℕ)) (a-i)) :=
homology.map _ _
  (arrow.hom_mk $ (begin
    have := (replacement_aux_snd_comm X a H (i+1)).symm.trans (category.assoc _ _ _).symm,
    rw [← X.X_eq_to_iso_d (show a - ↑(i + 2) = a - ↑(i + 1) - 1, by norm_num [sub_sub]),
      ← category.assoc] at this,
    exact this,
  end))
  (arrow.hom_mk (replacement_aux_snd_comm X a H i).symm) rfl

instance (i : ℕ) : mono (replacement_homology_map X a H i) :=
begin
  apply mono_homology_map_of_epi_pullback_lift,
  dsimp [replacement_aux],
  convert projective.π_epi _,
  apply pullback.hom_ext,
  { simpa only [category.comp_id, category.assoc, arrow.hom_mk_left, X.X_eq_to_iso_trans,
      X.X_eq_to_iso_refl, pullback.lift_fst] },
  { refine (cancel_mono (kernel.ι _)).mp _,
    simp only [category.comp_id, category.assoc, arrow.hom_mk_left, kernel.lift_ι,
      X.X_eq_to_iso_trans, pullback.lift_snd, X.X_eq_to_iso_refl],
    simp_rw ← category.assoc,
    exact category.comp_id _ },
end
.

lemma comp_left_epi_iff {V : Type*} [category V] {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) [epi f] :
  epi (f ≫ g) ↔ epi g :=
⟨λ h, @@epi_of_epi _ _ _ h, λ h, @@epi_comp _ _ _ _ h⟩

lemma comp_right_epi_iff {V : Type*} [category V] {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso g] :
  epi (f ≫ g) ↔ epi f :=
⟨λ h, by simpa using @@epi_comp _ (f ≫ g) h (inv g) _, λ h, @@epi_comp _ _ h _ _⟩

instance replacement_kernel_map_epi' (i : ℕ) :
  epi (kernel.lift (X.d (a - (i + 1)) (a - i))
    (kernel.ι (replacement_aux X a H (i + 1)).fst.hom ≫ (replacement_aux X a H (i + 1)).snd)
    (by { rw category.assoc,
      convert kernel_ι_replacement_aux_eq_zero X a H _; norm_num [sub_add] })) :=
begin
  convert projective.replacement_kernel_map_epi X a H _; norm_num [sub_add]
end

instance (i : ℕ) : epi (replacement_homology_map X a H i) :=
begin
  apply_with (epi_of_epi (homology.π _ _ _)) { instances := ff },
  erw homology.π_map,
  apply_with epi_comp { instances := ff },
  swap, { apply_instance },
  rw [← comp_left_epi_iff (kernel_subobject_iso _).inv,
    ← comp_right_epi_iff _ (kernel_subobject_iso _).hom],
  convert projective.replacement_kernel_map_epi' X a H _ using 1,
  refine (cancel_mono (kernel.ι _)).mp _,
  simp only [kernel_subobject_arrow'_assoc, category.assoc, kernel_subobject_map_arrow,
    kernel_subobject_arrow, arrow.hom_mk_left],
  erw kernel.lift_ι,
  apply_instance
end

instance (i : ℕ) : is_iso (replacement_homology_map X a H i) :=
is_iso_of_mono_of_epi _

-- lemma eeoo (i : ℕ) :
--   homology.map ((replacement X a H).d_comp_d _ _ _) (X.d_comp_d _ _ _)
--     (arrow.hom_mk ((replacement.hom X a H).comm (a - i - 1) (a - i)))
--     (arrow.hom_mk ((replacement.hom X a H).comm (a - i) (a - i + 1))) rfl ==
--   replacement_homology_map X a H i :=
-- begin
--   delta replacement_hom
-- end

lemma replacement_aux_eq_of_eq (i j : ℕ) (e : i + 1 = j) :
  (replacement_aux X a H j).1.right = (replacement_aux X a H i).1.left :=
begin
  subst e,
  dsimp [replacement_aux],
  refl
end

lemma replacement_aux_fst_hom_congr (i j : ℕ) (e : i = j) :
  (replacement_aux X a H i).1.hom == (replacement_aux X a H j).1.hom :=
by { subst e }

lemma replacement_aux_snd_congr (i j : ℕ) (e : i = j) :
  (replacement_aux X a H i).2 == (replacement_aux X a H j).2 :=
by { subst e }

def replacement_homology_eq (i : ℕ) :
  homology _ _ ((replacement X a H).d_comp_d (a - ↑(i + 1) - 1) (a - ↑(i + 1)) (a - i)) =
    homology _ _ (replacement_homology_map._proof_4 X a H i) :=
begin
  dsimp [replacement],
  have e₁ : a - (↑i + 1) - 1 + 1 = a - (↑i + 1) := by norm_num [sub_add],
  have e₂ :a - (↑i + 1) + 1 = a - ↑i := by norm_num [sub_add],
  have e₃ : ¬ a - (↑i + 1) - 1 > a :=
    by { simp only [gt_iff_lt, tsub_le_iff_right, not_lt], linarith },
  have e₄ : ¬a - (↑i + 1) > a := by { simp only [gt_iff_lt, tsub_le_iff_right, not_lt], linarith },
  have e₅ : ¬a - i > a := by { simp only [gt_iff_lt, tsub_le_iff_right, not_lt], linarith },
  have e₆ : (a - (a - (↑i + 1))).nat_abs = i + 1,
  { rw [← sub_add, sub_self, zero_add], exact int.nat_abs_of_nat_core _ },
  have e₇ : (a - (a - (↑i + 1) - 1)).nat_abs = i + 1 + 1,
  { rw [sub_sub, ← sub_add, sub_self, zero_add], exact int.nat_abs_of_nat_core _ },
  have e₈ : (a - (a - i)).nat_abs = i := by norm_num,
  simp only [dif_pos e₁, dif_pos e₂, dif_neg e₄, dif_neg e₅],
  congr' 1,
  { rw if_neg e₃, apply replacement_aux_eq_of_eq, rw e₇ },
  { rw if_neg e₄, apply replacement_aux_eq_of_eq, rw e₆ },
  { rw if_neg e₅, { congr, { ext, congr, exact e₈ }, { exact e₈ } } },
  { rw [eq_to_hom_comp_heq_iff, comp_eq_to_hom_heq_iff, category.comp_id, e₆] },
  { rw [eq_to_hom_comp_heq_iff, comp_eq_to_hom_heq_iff, e₈] },
end

lemma replacement_hom_homology_iso (i : ℕ) :
  homology.map ((replacement X a H).d_comp_d _ _ _) (X.d_comp_d _ _ _)
    (arrow.hom_mk ((replacement.hom X a H).comm _ _))
    (arrow.hom_mk ((replacement.hom X a H).comm _ _)) rfl =
  (eq_to_hom (replacement_homology_eq X a H i)) ≫ replacement_homology_map X a H i :=
begin
  rw [← heq_iff_eq, heq_eq_to_hom_comp_iff],
  delta replacement_homology_map,
  dsimp [replacement],
  congr' 3,
  any_goals { rw if_neg, apply replacement_aux_eq_of_eq,
    { norm_num [← sub_add], exact (int.nat_abs_of_nat_core _).symm },
    { simp only [gt_iff_lt, tsub_le_iff_right, not_lt], linarith } },
  any_goals { rw if_neg, dsimp [replacement_aux], congr, { ext, congr, norm_num }, { norm_num },
    { simp only [gt_iff_lt, tsub_le_iff_right, not_lt], linarith } },
  any_goals { rw category.comp_id },
  any_goals { rw heq_eq_to_hom_comp_iff},
  any_goals { delta homological_complex.X_eq_to_iso, erw heq_comp_eq_to_hom_iff },
  any_goals { dsimp [replacement.hom],
    rw [dif_neg, eq_to_hom_comp_heq_iff, eq_to_hom_comp_heq_iff],
    erw comp_eq_to_hom_heq_iff,
    { apply replacement_aux_snd_congr,
      refine eq.trans _ (int.nat_abs_of_nat_core _),
      congr' 1,
      norm_num [sub_sub, sub_add] },
    { simp only [gt_iff_lt, tsub_le_iff_right, not_lt], linarith } },
  all_goals { rw [dif_pos, dif_neg, eq_to_hom_comp_heq_iff, comp_eq_to_hom_heq_iff],
    apply replacement_aux_fst_hom_congr,
    { congr' 1,
      refine eq.trans _ (int.nat_abs_of_nat_core _),
      congr' 1,
      norm_num [sub_sub, sub_add] },
    { simp only [gt_iff_lt, tsub_le_iff_right, not_lt], linarith },
    { norm_num [sub_sub, sub_add] } },
end
.

lemma homology_functor_map_iso' {X Y : cochain_complex V ℤ} (f : X ⟶ Y) (i j k : ℤ)
  (e₁ : i + 1 = j) (e₂ : j + 1 = k) :
  (homology_functor V (complex_shape.up ℤ) j).map f =
    (homology_functor_obj_iso X _).hom ≫
      (eq_to_hom $ by { have e₁ : i = j - 1 := by simp [← e₁], substs e₁ e₂ }) ≫
    homology.map (X.d_comp_d i j k) (Y.d_comp_d i j k)
      (arrow.hom_mk (f.comm i j)) (arrow.hom_mk (f.comm j k)) rfl ≫
    (eq_to_hom $ by { have e₁ : i = j - 1 := by simp [← e₁], substs e₁ e₂ }) ≫
      (homology_functor_obj_iso Y _).inv :=
begin
  have e₁ : i = j - 1 := by simp [← e₁], substs e₁ e₂,
  erw [category.id_comp, category.id_comp],
  rw homology_functor_map_iso
end

include H

lemma homology_is_zero_object_of_bounded (i : ℤ) (e : a ≤ i) :
  is_zero_object ((homology_functor V (complex_shape.up ℤ) i).obj X) :=
begin
  apply is_zero_object_of_mono (homology_iso_cokernel_image_to_kernel' _ _ _).hom,
  apply is_zero_object_of_epi (cokernel.π _),
  apply is_zero_object_of_mono (kernel.ι _),
  apply H i e,
  all_goals { apply_instance }
end

omit H

lemma replacement_is_projective (i : ℤ) : projective ((replacement X a H).X i) :=
begin
  dsimp [replacement],
  split_ifs,
  { apply_instance },
  { dsimp [replacement_aux],
    induction (a - i).nat_abs; dsimp [replacement_aux]; apply_instance }
end

instance (i : ℤ) : epi ((replacement.hom X a H).f i) :=
begin
  dsimp [replacement.hom],
  split_ifs,
  { apply epi_of_is_zero_object, apply H, exact le_of_lt h },
  { apply_instance }
end

lemma replacement_is_bounded : ∀ i (h : a ≤ i), is_zero_object ((replacement X a H).X i) :=
begin
  intros i h,
  dsimp [replacement],
  split_ifs,
  { exact zero_is_zero_object },
  { have : a = i := by linarith, subst this,
    rw [sub_self, int.nat_abs_zero],
    dsimp [replacement_aux],
    exact zero_is_zero_object }
end

instance : quasi_iso (replacement.hom X a H) :=
begin
  constructor,
  intro i,
  rw ← sub_add_cancel i a,
  induction (i - a) with i i,
  { apply is_iso_of_is_zero_object,
    exact homology_is_zero_object_of_bounded _ a (replacement_is_bounded X a H) _ (by simp),
    exact homology_is_zero_object_of_bounded _ a H _ (by simp) },
  { rw (show (-[1+ i] + a) = (a - ↑(i + 1)), by { rw [add_comm], refl }),
    rw homology_functor_map_iso' _ (a - ↑(i + 1) - 1) (a - ↑(i + 1)) (a - i),
    { rw replacement_hom_homology_iso X a H i,
      apply_instance },
    { norm_num },
    { norm_num [sub_add] },
    apply_instance }
end
.


end category_theory.projective
