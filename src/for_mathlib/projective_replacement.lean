import category_theory.abelian.projective
import for_mathlib.homological_complex_shift
import tactic.linarith
import algebra.homology.quasi_iso
import algebra.homology.homotopy
import for_mathlib.abelian_category
import for_mathlib.homology

.

open category_theory category_theory.limits

open_locale zero_object

section zero_object

variables {V : Type*} [category V] [has_zero_morphisms V]

lemma is_zero_iff_id_eq_zero {X : V} : is_zero X ↔ 𝟙 X = 0 :=
begin
  split,
  { exact λ h, h.1 _, },
  { intro e,
    exact ⟨λ _ _, by { rw [← cancel_epi (𝟙 _), e, comp_zero, zero_comp], apply_instance },
      λ _ _, by { rw [← cancel_mono (𝟙 _), e, comp_zero, zero_comp], apply_instance }⟩, }
end

lemma is_zero_of_mono {X Y : V} (f : X ⟶ Y) [mono f] (h : is_zero Y) : is_zero X :=
by rw [is_zero_iff_id_eq_zero, ← cancel_mono f, zero_comp, h.2 (𝟙 _ ≫ f)]

lemma is_zero_of_epi {X Y : V} (f : X ⟶ Y) [epi f] (h : is_zero X) : is_zero Y :=
by rw [is_zero_iff_id_eq_zero, ← cancel_epi f, comp_zero, h.1 (f ≫ 𝟙 Y)]

noncomputable
lemma split_epi_of_is_zero {X Y : V} (f : X ⟶ Y) (h : is_zero Y) : split_epi f :=
⟨0, by simp [is_zero_iff_id_eq_zero.mp h]⟩

lemma epi_of_is_zero {X Y : V} (f : X ⟶ Y) (h : is_zero Y) : epi f :=
@@split_epi.epi _ _ (split_epi_of_is_zero f h)

noncomputable
lemma split_mono_of_is_zero {X Y : V} (f : X ⟶ Y) (h : is_zero X) : split_mono f :=
⟨0, by simp [is_zero_iff_id_eq_zero.mp h]⟩

lemma mono_of_is_zero_object {X Y : V} (f : X ⟶ Y) (h : is_zero X) : mono f :=
@@split_mono.mono _ _ (split_mono_of_is_zero f h)

lemma is_iso_of_is_zero {X Y : V} (f : X ⟶ Y)
  (h₁ : is_zero X) (h₂ : is_zero Y) : is_iso f :=
begin
  use 0,
  rw [is_zero_iff_id_eq_zero.mp h₁, is_zero_iff_id_eq_zero.mp h₂],
  split; simp
end

end zero_object

variables {V : Type*} [category V] [abelian V] [enough_projectives V] (X : cochain_complex V ℤ)
variables (a : ℤ) (H : ∀ i (h : a ≤ i), is_zero (X.X i))

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
    { rw comp_zero, apply (H _ (le_of_lt h)).2 },
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

instance : mono (homology.ι f g w) :=
by { delta homology.ι, apply_instance }

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
lemma homology.π'_ι :
  homology.π' f g w ≫ homology.ι f g w = kernel.ι g ≫ cokernel.π f :=
by { delta homology.π' homology.ι homology_iso_kernel_desc, simp }

@[simp, reassoc]
lemma homology.π_ι :
  homology.π f g w ≫ homology.ι f g w = (kernel_subobject _).arrow ≫ cokernel.π _ :=
by rw [← homology.π'_eq_π, category.assoc, homology.π'_ι, kernel_subobject_arrow_assoc]

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
  apply pseudoelement.pseudo_injective_of_mono (homology.ι f' g' w'),
  simpa [← pseudoelement.comp_apply, p] using e₂,
end

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
  { dsimp [replacement_aux], simp },
  { have : a - i.succ + 1 = a - i, { norm_num [sub_add] },
    rw [this, ← replacement_aux_snd_comm, kernel.condition_assoc, zero_comp] }
end

instance replacement_kernel_map_epi (i : ℕ) : epi (kernel.lift (X.d (a - i) (a - i + 1))
    (kernel.ι (replacement_aux X a H i).fst.hom ≫ (replacement_aux X a H i).snd)
    (by rw [category.assoc, kernel_ι_replacement_aux_eq_zero])) :=
begin
  cases i,
  { apply epi_of_is_zero,
    apply is_zero_of_mono (kernel.ι _),
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
  { apply epi_of_is_zero, apply H, simp },
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
  { simp only [category.comp_id, category.id_comp] },
  { simp only [category.comp_id, category.id_comp] },
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

lemma homology_is_zero_of_bounded (i : ℤ) (e : a ≤ i) :
  is_zero ((homology_functor V (complex_shape.up ℤ) i).obj X) :=
begin
  apply is_zero_of_mono (homology_iso_cokernel_image_to_kernel' _ _ _).hom,
  apply is_zero_of_epi (cokernel.π _),
  apply is_zero_of_mono (kernel.ι _),
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
  { apply epi_of_is_zero, apply H, exact le_of_lt h },
  { apply_instance }
end

lemma replacement_is_bounded : ∀ i (h : a ≤ i), is_zero ((replacement X a H).X i) :=
begin
  intros i h,
  dsimp [replacement],
  split_ifs,
  { exact is_zero_zero _ },
  { have : a = i := by linarith, subst this,
    rw [sub_self, int.nat_abs_zero],
    dsimp [replacement_aux],
    exact is_zero_zero _ }
end

instance : quasi_iso (replacement.hom X a H) :=
begin
  constructor,
  intro i,
  rw ← sub_add_cancel i a,
  induction (i - a) with i i,
  { apply is_iso_of_is_zero,
    exact homology_is_zero_of_bounded _ a (replacement_is_bounded X a H) _ (by simp),
    exact homology_is_zero_of_bounded _ a H _ (by simp) },
  { rw (show (-[1+ i] + a) = (a - ↑(i + 1)), by { rw [add_comm], refl }),
    rw homology_functor_map_iso' _ (a - ↑(i + 1) - 1) (a - ↑(i + 1)) (a - i),
    { rw replacement_hom_homology_iso X a H i,
      apply_instance },
    { norm_num },
    { norm_num [sub_add] },
    apply_instance }
end
.

@[simps]
def _root_.cochain_complex.as_nat_chain_complex (X : cochain_complex V ℤ) (a : ℤ) :
  chain_complex V ℕ :=
{ X := λ i, X.X (a - i),
  d := λ i j, X.d _ _,
  shape' := λ i j r, by { refine X.shape _ _ (λ e, r _), dsimp at e ⊢,
    apply int.coe_nat_inj, dsimp, linarith },
  d_comp_d' := λ i j k _ _, X.d_comp_d _ _ _ }

@[simps]
def _root_.cochain_complex.to_nat_chain_complex (a : ℤ) :
  cochain_complex V ℤ ⥤ chain_complex V ℕ :=
{ obj := λ X, X.as_nat_chain_complex a,
  map := λ X Y f, { f := λ i, f.f _ } }

lemma is_zero_iff_iso_zero (X : V) :
  is_zero X ↔ nonempty (X ≅ 0) :=
⟨λ e, ⟨e.iso_zero⟩, λ ⟨e⟩, is_zero_of_iso_of_zero (is_zero_zero _) e.symm⟩

lemma preadditive.exact_iff_homology_is_zero {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) :
  exact f g ↔ ∃ w, is_zero (homology f g w) :=
begin
  rw preadditive.exact_iff_homology_zero,
  simp_rw is_zero_iff_iso_zero,
end

noncomputable
def null_homotopic_of_projective_to_acyclic_aux {X Y : cochain_complex V ℤ} (f : X ⟶ Y) (a : ℤ)
  (h₁ : ∀ i, projective (X.X i))
  (h₂ : ∀ i, a ≤ i → is_zero (X.X i))
  (h₃ : ∀ i, is_zero ((homology_functor _ _ i).obj Y)) :
  homotopy ((cochain_complex.to_nat_chain_complex a).map f) 0 :=
begin
  have h₄ : ∀ i, a ≤ i → f.f i = 0,
  { intros i e, apply (h₂ i e).1 },
  fapply homotopy.mk_inductive _ 0,
  { dsimp, rw zero_comp, apply h₄, linarith },
  all_goals { dsimp },
  { have := f.comm (a - (0 + 1)) a,
    rw [h₄ _ (le_of_eq rfl), comp_zero] at this,
    refine projective.factor_thru (kernel.lift _ _ this) _,
    exact kernel.lift _ _ (Y.d_comp_d _ _ _),
    { apply_with kernel.lift.epi { instances := ff },
      rw preadditive.exact_iff_homology_is_zero,
      refine ⟨Y.d_comp_d _ _ _,
        is_zero_of_iso_of_zero (h₃ (a - (0 + 1))) (homology_iso _ _ _ _ _ _)⟩,
      all_goals { dsimp, abel } } },
  { rw comp_zero, conv_rhs { rw [zero_add] },
    slice_rhs 2 3 { rw ← kernel.lift_ι _ _ (Y.d_comp_d (a - (0 + 1 + 1)) (a - (0 + 1)) a) },
    rw [← category.assoc, projective.factor_thru_comp, kernel.lift_ι] },
  { rintros n ⟨g₁, g₂, e⟩, dsimp only,
    have : X.d (a - (n + 1 + 1)) (a - (n + 1)) ≫
      (f.f (a - (↑n + 1)) - g₂ ≫ Y.d (a - (↑n + 1 + 1)) (a - (↑n + 1))) = 0,
    { rw ← sub_eq_iff_eq_add at e, rw [e, X.d_comp_d_assoc, zero_comp] },
    rw [preadditive.comp_sub, ← f.comm, ← category.assoc, ← preadditive.sub_comp] at this,
    fsplit,
    { refine projective.factor_thru (kernel.lift _ _ this) _,
      exact kernel.lift _ _ (Y.d_comp_d _ _ _),
      apply_with kernel.lift.epi { instances := ff },
      rw preadditive.exact_iff_homology_is_zero,
      refine ⟨Y.d_comp_d _ _ _, is_zero_of_iso_of_zero (h₃ _) (homology_iso _ _ _ _ _ _)⟩,
      all_goals { dsimp, abel } },
    { rw ← sub_eq_iff_eq_add',
      slice_rhs 2 3 { rw ← kernel.lift_ι (Y.d (a-(n+1+1)) (a-(n+1))) _ (Y.d_comp_d _ _ _) },
      rw [← category.assoc, projective.factor_thru_comp, kernel.lift_ι] } }
end

noncomputable
def null_homotopic_of_projective_to_acyclic {X Y : cochain_complex V ℤ} (f : X ⟶ Y) (a : ℤ)
  (h₁ : ∀ i, projective (X.X i))
  (h₂ : ∀ i, a ≤ i → is_zero (X.X i))
  (h₃ : ∀ i, is_zero ((homology_functor _ _ i).obj Y)) :
  homotopy f 0 :=
{ hom := λ i j, if h : i ≤ a ∧ j ≤ a then begin
    refine (X.X_eq_to_iso _).hom ≫ (null_homotopic_of_projective_to_acyclic_aux f a h₁ h₂ h₃).hom
      (a - i).nat_abs (a - j).nat_abs ≫ (Y.X_eq_to_iso _).hom,
    swap, symmetry,
    all_goals { rw [← int.abs_eq_nat_abs, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', abs_eq_self],
      cases h, rwa sub_nonneg }
  end else 0,
  zero' := begin
    intros i j e,
    split_ifs,
    { cases h,
      rw [(null_homotopic_of_projective_to_acyclic_aux f a h₁ h₂ h₃).zero, zero_comp, comp_zero],
      intro e', apply e,
      dsimp at e' ⊢,
      apply_fun (coe : ℕ → ℤ) at e',
      rw [int.coe_nat_add, ← int.abs_eq_nat_abs, ← int.abs_eq_nat_abs, abs_eq_self.mpr _,
        abs_eq_self.mpr _, int.coe_nat_one, sub_add, sub_right_inj] at e',
      rw [← e', sub_add_cancel],
      all_goals { rwa sub_nonneg } },
    { refl }
  end,
  comm := begin
    intros i,
    rw [d_next_eq _ (show (complex_shape.up ℤ).rel i (i+1), from rfl),
      prev_d_eq _ (show (complex_shape.up ℤ).rel (i-1) i, from sub_add_cancel _ _)],
    have e₁ : i + 1 ≤ a ∧ i ≤ a ↔ i + 1 ≤ a := by { rw and_iff_left_iff_imp, intro e, linarith },
    have e₂ : i ≤ a ∧ i - 1 ≤ a ↔ i ≤ a := by { rw and_iff_left_iff_imp, intro e, linarith },
    split_ifs; rw e₁ at h; rw e₂ at h_1,
    { have e : a - (a - i).nat_abs = i,
      { rw [← int.abs_eq_nat_abs, abs_eq_self.mpr _, ← sub_add, sub_self, zero_add],
        rwa sub_nonneg },
      rw [← cancel_mono (Y.X_eq_to_iso e.symm).hom, ← cancel_epi (X.X_eq_to_iso e).hom],
      dsimp,
      simp only [homological_complex.X_d_eq_to_iso_assoc, category.comp_id, add_zero,
        homological_complex.X_d_eq_to_iso, category.id_comp,
        homological_complex.X_eq_to_iso_d_assoc, homological_complex.X_eq_to_iso_trans_assoc,
        preadditive.comp_add, category.assoc, homological_complex.X_eq_to_iso_d,
        homological_complex.X_eq_to_iso_trans, homological_complex.X_eq_to_iso_f_assoc,
        homological_complex.X_eq_to_iso_refl, preadditive.add_comp],
      have := (null_homotopic_of_projective_to_acyclic_aux f a h₁ h₂ h₃).comm (a - i).nat_abs,
      dsimp at this,
      rw [this, add_zero],
      congr' 1,
      { apply d_next_eq, dsimp, apply int.coe_nat_inj, norm_num [← int.abs_eq_nat_abs],
        rw [abs_eq_self.mpr _, abs_eq_self.mpr _, sub_add, add_sub_cancel],
        all_goals { rwa sub_nonneg } },
      { apply prev_d_eq, dsimp, apply int.coe_nat_inj, norm_num [← int.abs_eq_nat_abs],
        rw [abs_eq_self.mpr _, abs_eq_self.mpr _, ← sub_add],
        all_goals { rw sub_nonneg, linarith } } },
    { exfalso, linarith },
    { have : a = i := by linarith, subst this,
      suffices : (null_homotopic_of_projective_to_acyclic_aux f a h₁ h₂ h₃).hom
        (a - a).nat_abs (a - (a - 1)).nat_abs = 0,
      { rw this,
        simp only [add_zero, limits.comp_zero, homological_complex.zero_f_apply,
          limits.zero_comp], apply (h₂ _ h_1).1 },
        rw [← sub_add, sub_self, zero_add, int.nat_abs_zero, int.nat_abs_one],
        dsimp [null_homotopic_of_projective_to_acyclic_aux, homotopy.mk_inductive],
        rw [dif_pos (zero_add _), zero_comp, zero_comp] },
    { simp only [add_zero, limits.comp_zero, homological_complex.zero_f_apply,
        limits.zero_comp], apply (h₂ _ _).1, linarith }
  end }

end category_theory.projective
