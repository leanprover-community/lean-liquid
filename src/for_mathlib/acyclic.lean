import category_theory.preadditive.additive_functor
import category_theory.limits.preserves.shapes.biproducts

import for_mathlib.derived.les2
import for_mathlib.derived.les_facts
import for_mathlib.derived.Ext_lemmas

import for_mathlib.is_quasi_iso
import for_mathlib.short_exact
import for_mathlib.homology
import for_mathlib.exact_lift_desc
import for_mathlib.additive_functor
import for_mathlib.homotopy_category_lemmas
import for_mathlib.homology_lift_desc

.

noncomputable theory

open category_theory category_theory.limits opposite
open homotopy_category (hiding single)
open bounded_homotopy_category

universes v v' u u'

-- main proof in this file is inspired by https://math.stackexchange.com/a/2118042

section

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐] {ι : Type*} {c : complex_shape ι}

def delta_to_kernel (C : homological_complex 𝓐 c) (i j k : ι) :
  C.X i ⟶ kernel (C.d j k) :=
factor_thru_image _ ≫ image_to_kernel' (C.d i j) _ (C.d_comp_d _ _ _)

def delta_to_kernel_ι (C : homological_complex 𝓐 c) (i j k : ι) :
  delta_to_kernel C i j k ≫ kernel.ι (C.d j k) = C.d i j :=
begin
  delta delta_to_kernel image_to_kernel',
  rw [category.assoc, kernel.lift_ι, image.fac],
end

def d_delta_to_kernel (C : homological_complex 𝓐 c) (h i j k : ι) :
  C.d h i ≫ delta_to_kernel C i j k = 0 :=
begin
  rw [← cancel_mono (kernel.ι (C.d j k)), category.assoc, delta_to_kernel_ι, C.d_comp_d, zero_comp],
end

-- move me
lemma short_exact_comp_iso {A B C D : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (hh : is_iso h) :
  short_exact f (g ≫ h) ↔ short_exact f g :=
begin
  split; intro H,
  { haveI : mono f := H.mono,
    haveI : epi g,
    { haveI := H.epi, have := epi_comp (g ≫ h) (inv h), simpa only [category.assoc, is_iso.hom_inv_id, category.comp_id] },
    refine ⟨_⟩, have := H.exact, rwa exact_comp_iso at this, },
  { haveI : mono f := H.mono,
    haveI : epi g := H.epi,
    haveI : epi (g ≫ h) := epi_comp g h,
    refine ⟨_⟩, have := H.exact, rwa exact_comp_iso }
end

lemma is_acyclic_def
  (C : homotopy_category 𝓐 c) :
  is_acyclic C ↔ (∀ i, is_zero (C.as.homology i)) :=
begin
  split,
  { apply is_acyclic.cond },
  { apply is_acyclic.mk }
end

lemma is_acyclic_iff_short_exact_to_cycles
  (C : homotopy_category 𝓐 (complex_shape.up ℤ)) :
  is_acyclic C ↔
  (∀ i, short_exact (kernel.ι (C.as.d i (i+1))) (delta_to_kernel C.as i (i+1) (i+1+1))) :=
begin
  rw is_acyclic_def,
  symmetry,
  apply (equiv.add_right (1 : ℤ)).forall_congr,
  intro i,
  let e := (homology_iso C.as i (i+1) (i+1+1) rfl rfl),
  dsimp [delta_to_kernel] at e ⊢,
  rw [e.is_zero_iff, homology_is_zero_iff_image_to_kernel'_is_iso],
  split,
  { apply iso_of_short_exact_comp_right _ _ _, apply short_exact_kernel_factor_thru_image },
  { intro h, rw short_exact_comp_iso _ _ _ h, apply short_exact_kernel_factor_thru_image }
end

lemma is_acyclic_iff_short_exact_to_cycles'
  (C : homological_complex 𝓐 (complex_shape.down ℤ)) :
  (∀ i, is_zero (C.homology i)) ↔
  (∀ i, short_exact (kernel.ι (C.d (i+1+1) (i+1))) (delta_to_kernel C (i+1+1) (i+1) i)) :=
begin
  symmetry,
  apply (equiv.add_right (1 : ℤ)).forall_congr,
  intro i,
  let e := (homology_iso C (i+1+1) (i+1) i rfl rfl),
  dsimp [delta_to_kernel] at e ⊢,
  rw [e.is_zero_iff, homology_is_zero_iff_image_to_kernel'_is_iso],
  split,
  { apply iso_of_short_exact_comp_right _ _ _, apply short_exact_kernel_factor_thru_image },
  { intro h, rw short_exact_comp_iso _ _ _ h, apply short_exact_kernel_factor_thru_image }
end

end

variables {𝓐 𝓑 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables [category 𝓑] [abelian 𝓑] [enough_projectives 𝓑]

variables (C : cochain_complex 𝓐 ℤ)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj C)]

def category_theory.functor.single (F : bounded_homotopy_category 𝓐 ⥤ 𝓑) (i : ℤ) : 𝓐 ⥤ 𝓑 :=
bounded_homotopy_category.single _ i ⋙ F

-- move me
lemma category_theory.limits.is_zero.biprod {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  {X Y : 𝓐} (hX : is_zero X) (hY : is_zero Y) :
  is_zero (X ⊞ Y) :=
begin
  rw is_zero_iff_id_eq_zero at hX hY ⊢,
  ext; simp [hX, hY],
end

instance category_theory.limits.preserves_binary_biproduct_of_additive
  {𝓐 𝓑 : Type*} [category.{v} 𝓐] [category.{v} 𝓑] [abelian 𝓐] [abelian 𝓑]
  (F : 𝓐 ⥤ 𝓑) [functor.additive F] (X Y : 𝓐) :
  preserves_binary_biproduct X Y F :=
preserves_binary_biproduct_of_preserves_biproduct _ _ _

lemma acyclic_left_of_short_exact (B : 𝓐) {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g)
  (hY : ∀ i > 0, is_zero (((Ext' i).obj (op $ Y)).obj B))
  (hZ : ∀ i > 0, is_zero (((Ext' i).obj (op $ Z)).obj B)) :
  ∀ i > 0, is_zero (((Ext' i).obj (op $ X)).obj B) :=
begin
  intros i hi,
  have := hfg.Ext'_five_term_exact_seq B i,
  refine (this.drop 1).pair.is_zero_of_is_zero_is_zero (hY _ hi) (hZ _ _),
  transitivity i, { exact lt_add_one i }, { exact hi }
end
.

lemma map_is_acyclic_of_acyclic_aux
  {A B C D X Y Z W : 𝓐} (f : A ⟶ B) (g : C ⟶ D) (π : B ⟶ kernel g)
  {α : X ⟶ B} {β : B ⟶ Y} {γ : Y ⟶ C} {δ : C ⟶ Z} {ε : Z ⟶ D} {ζ : D ⟶ W}
  (hαβ : short_exact α β) (hγδ : short_exact γ δ) (hεζ : short_exact ε ζ)
  (hf : mono f) (hfπ : exact f π)
  (hαπ : α ≫ π = 0) (hγg : γ ≫ g = 0) (hδε : δ ≫ ε = g)
  (hπι : π ≫ kernel.ι g = β ≫ γ) :
  short_exact f π :=
begin
  suffices : epi π, { resetI, exact ⟨hfπ⟩ },
  have hβ : epi β := hαβ.epi,
  have hγ : mono γ := hγδ.mono,
  have hε : mono ε := hεζ.mono,
  resetI,
  have hιδ : kernel.ι g ≫ δ = 0,
  { rw [← cancel_mono ε, category.assoc, hδε, kernel.condition, zero_comp], },
  let e1 : Y ⟶ kernel g := hαβ.exact.epi_desc π hαπ,
  let e2 : Y ⟶ kernel g := kernel.lift g γ hγg,
  let e3 : kernel g ⟶ Y := hγδ.exact.mono_lift (kernel.ι g) hιδ,
  have he12 : e1 = e2,
  { rw [← cancel_epi β, ← cancel_mono (kernel.ι g)],
    simp only [hπι, category.assoc, kernel.lift_ι, exact.comp_epi_desc_assoc], },
  have he13 : e1 ≫ e3 = 𝟙 _,
  { rw [he12, ← cancel_mono γ, category.assoc, exact.mono_lift_comp, kernel.lift_ι, category.id_comp], },
  have he31 : e3 ≫ e1 = 𝟙 _,
  { rw [he12, ← cancel_mono (kernel.ι g), category.assoc, kernel.lift_ι, exact.mono_lift_comp, category.id_comp], },
  let e : Y ≅ kernel g := ⟨e1, e3, he13, he31⟩,
  have hπ : β ≫ e.hom = π := exact.comp_epi_desc _ _ _,
  rw ← hπ, exact epi_comp _ _,
end

lemma short_exact_Ext_of_short_exact_of_acyclic {A B C : 𝓐} (Z : 𝓐) {f : A ⟶ B} {g : B ⟶ C}
  (hfg : short_exact f g) (hC : ∀ i > 0, is_zero (((Ext' i).obj (op $ C)).obj Z)) :
  short_exact (((Ext' 0).flip.obj Z).map g.op) (((Ext' 0).flip.obj Z).map f.op) :=
begin
  have H0 := hfg.Ext'_five_term_exact_seq Z 0,
  apply_with short_exact.mk {instances:=ff},
  { have H := ((hfg.Ext'_five_term_exact_seq Z (-1)).drop 2).pair,
    apply H.mono_of_is_zero,
    apply Ext'_is_zero_of_neg, dec_trivial },
  { apply (H0.drop 1).pair.epi_of_is_zero,
    apply hC, dec_trivial },
  { exact H0.pair }
end

lemma map_is_acyclic_of_acyclic''
  [is_acyclic ((homotopy_category.quotient _ _).obj C)]
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B)) :
  ∀ i, is_zero (((((Ext' 0).flip.obj B).map_homological_complex _).obj C.op).homology i) :=
begin
  rw is_acyclic_iff_short_exact_to_cycles',
  obtain ⟨a, ha⟩ := is_bounded_above.cond ((quotient 𝓐 (complex_shape.up ℤ)).obj C),
  have aux : ((quotient 𝓐 (complex_shape.up ℤ)).obj C).is_acyclic := ‹_›,
  rw is_acyclic_iff_short_exact_to_cycles at aux,
  intro i,
  let K := λ j, kernel (C.d j (j+1)),
  suffices hK : ∀ j, ∀ i > 0, is_zero (((Ext' i).obj (op $ K j)).obj B),
  { have SES1 := short_exact_Ext_of_short_exact_of_acyclic B (aux (i+1+1)) (hK _),
    have SES2 := short_exact_Ext_of_short_exact_of_acyclic B (aux (i+1)) (hK _),
    have SES3 := short_exact_Ext_of_short_exact_of_acyclic B (aux i) (hK _),
    apply map_is_acyclic_of_acyclic_aux _ _ _ SES1 SES2 SES3 infer_instance;
      clear SES1 SES2 SES3 aux,
    { delta delta_to_kernel image_to_kernel',
      apply exact_comp_mono, rw exact_factor_thru_image_iff, exact exact_kernel_ι },
    { rw [← cancel_mono (kernel.ι _), zero_comp, category.assoc, delta_to_kernel_ι],
      swap, apply_instance,
      erw [functor.map_homological_complex_obj_d, ← functor.map_comp],
      dsimp only [homological_complex.op_d, quotient_obj_as],
      rw [← op_comp, d_delta_to_kernel, op_zero, functor.map_zero], },
    { erw [functor.map_homological_complex_obj_d, ← functor.map_comp],
      dsimp only [homological_complex.op_d, quotient_obj_as],
      rw [← op_comp, d_delta_to_kernel, op_zero, functor.map_zero], },
    { rw [← functor.map_comp, ← op_comp, delta_to_kernel_ι], refl, },
    { rw [delta_to_kernel_ι, ← functor.map_comp, ← op_comp, delta_to_kernel_ι], refl, },
    { apply_instance } },
  clear i, intro j,
  have : ∀ j ≥ a, ∀ i > 0, is_zero (((Ext' i).obj (op $ K j)).obj B),
  { intros j hj i hi,
    apply bounded_derived_category.Ext'_zero_left_is_zero,
    apply is_zero.op,
    refine is_zero.of_mono (kernel.ι _) _,
    exact ha j hj },
  apply int.induction_on' j a,
  { exact this _ le_rfl, },
  { intros j hj aux, apply this, exact int.le_add_one hj, },
  { intros j hj IH,
    obtain ⟨j, rfl⟩ : ∃ i, i + 1 = j := ⟨j - 1, sub_add_cancel _ _⟩,
    rw add_sub_cancel,
    apply acyclic_left_of_short_exact B (kernel.ι _) (delta_to_kernel _ _ _ _) _ (hC _) IH,
    exact aux j, }
end

lemma map_is_acyclic_of_acyclic'
  [is_acyclic ((homotopy_category.quotient _ _).obj C)]
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B)) :
  is_acyclic ((((Ext' 0).flip.obj B).right_op.map_homotopy_category _).obj ((homotopy_category.quotient _ _).obj C)) :=
begin
  rw is_acyclic_def,
  intro i,
  have h1 : (complex_shape.up ℤ).rel (i - 1) i, { dsimp, apply sub_add_cancel },
  refine is_zero.of_iso _ (homology_iso' _ (i-1) i (i+1) h1 rfl),
  dsimp only [functor.map_homotopy_category_obj, quotient_obj_as,
    functor.right_op_map, functor.map_homological_complex_obj_d],
  apply exact.homology_is_zero,
  apply exact.op,
  refine exact_of_homology_is_zero _,
  { rw [← category_theory.functor.map_comp, ← op_comp, homological_complex.d_comp_d, op_zero, functor.map_zero], },
  have := map_is_acyclic_of_acyclic'' C B hC i,
  apply this.of_iso _, clear this,
  let C' := (((Ext' 0).flip.obj B).map_homological_complex (complex_shape.up ℤ).symm).obj (homological_complex.op C),
  have h1 : (complex_shape.down ℤ).rel i (i - 1), { dsimp, apply sub_add_cancel },
  exact (homology_iso' C' (i+1) i (i-1) rfl h1).symm,
end

lemma map_is_acyclic_of_acyclic
  [is_acyclic ((homotopy_category.quotient _ _).obj C)]
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B)) :
  is_acyclic (((preadditive_yoneda.obj B).right_op.map_homotopy_category _).obj ((homotopy_category.quotient _ _).obj C)) :=
begin
  have := map_is_acyclic_of_acyclic' C B hC,
  rw is_acyclic_def at this ⊢,
  intro i, specialize this i,
  apply this.of_iso _, clear this,
  have h1 : (complex_shape.up ℤ).rel (i - 1) i, { dsimp, apply sub_add_cancel },
  refine (homology_iso' _ (i-1) i (i+1) h1 rfl) ≪≫ _ ≪≫ (homology_iso' _ (i-1) i (i+1) h1 rfl).symm,
  dsimp only [functor.map_homotopy_category_obj, quotient_obj_as,
    functor.right_op_map, functor.map_homological_complex_obj_d],
  let e := λ i, ((bounded_derived_category.Ext'_zero_flip_iso _ B).app (op $ C.X i)).op,
  refine homology.map_iso _ _ (arrow.iso_mk (e _) (e _) _) (arrow.iso_mk (e _) (e _) _) rfl,
  { simp only [iso.op_hom, iso.app_hom, arrow.mk_hom, functor.flip_obj_map, ← op_comp, ← nat_trans.naturality], },
  { simp only [iso.op_hom, iso.app_hom, arrow.mk_hom, functor.flip_obj_map, ← op_comp, ← nat_trans.naturality], },
end

lemma acyclic_of_projective (P B : 𝓐) [projective P] (i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (op P)).obj B) :=
begin
  rw (Ext'_iso (op P) B i _ (𝟙 _) _).is_zero_iff,
  { rcases i with ((_|i)|i),
    { exfalso, revert hi, dec_trivial },
    swap, { exfalso, revert hi, dec_trivial },
    refine is_zero.homology_is_zero _ _ _ _,
    apply AddCommGroup.is_zero_of_eq,
    intros,
    apply is_zero.eq_of_src,
    apply is_zero_zero, },
  { refine ⟨_, _, _⟩,
    { rintro (_|n), { assumption }, { dsimp, apply_instance } },
    { exact exact_zero_mono (𝟙 P) },
    { rintro (_|n); exact exact_of_zero 0 0 } }
end

def Ext_compute_with_acyclic_aux₁
  (B : 𝓐)
  (i : ℤ) :
  ((Ext i).obj (op $ of' C)).obj ((single _ 0).obj B) ≅
  (preadditive_yoneda.obj ((single 𝓐 (-i)).obj B)).obj (op (of' C).replace) :=
(preadditive_yoneda.map_iso $ (shift_single_iso 0 i).app B ≪≫ eq_to_iso (by rw zero_sub)).app _

abbreviation of'_hom {C₁ C₂ : cochain_complex 𝓐 ℤ}
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₁).is_bounded_above]
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₂).is_bounded_above]
  (f : C₁ ⟶ C₂) :
  of' C₁ ⟶ of' C₂ :=
(homotopy_category.quotient _ _).map f

lemma Ext_compute_with_acyclic_aux₁_naturality
  (C₁ C₂ : cochain_complex 𝓐 ℤ)
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₁).is_bounded_above]
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₂).is_bounded_above]
  (B : 𝓐)
  (f : C₁ ⟶ C₂)
  (i : ℤ) :
  ((Ext i).map $ quiver.hom.op $ of'_hom f).app _ ≫
    (Ext_compute_with_acyclic_aux₁ C₁ B i).hom =
  (Ext_compute_with_acyclic_aux₁ C₂ B i).hom ≫
  (preadditive_yoneda.obj _).map (quiver.hom.op $
  bounded_homotopy_category.lift ((of' C₁).π ≫ of'_hom f) (of' C₂).π) :=
begin
  ext F,
  dsimp [Ext, Ext_compute_with_acyclic_aux₁],
  simp only [comp_apply],
  dsimp, simp,
end

def Ext_compute_with_acyclic_aux₂
  (B : 𝓐)
  (i : ℤ) :
  (preadditive_yoneda.obj ((single 𝓐 (-i)).obj B)).obj (op (of' C).replace) ≅
  (((preadditive_yoneda.obj B).map_homological_complex (complex_shape.up ℤ).symm).obj
  ((of' C).replace).val.as.op).homology (-i) :=
  hom_single_iso _ _ _

-- TODO: We should prove naturality of `hom_single_iso` independently!
lemma Ext_compute_with_acyclic_aux₂_naturality
  (C₁ C₂ : cochain_complex 𝓐 ℤ)
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₁).is_bounded_above]
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₂).is_bounded_above]
  (B : 𝓐)
  (f : C₁ ⟶ C₂)
  (i : ℤ) :
  (preadditive_yoneda.obj _).map (quiver.hom.op $
    bounded_homotopy_category.lift ((of' C₁).π ≫ of'_hom f) (of' C₂).π) ≫
    (Ext_compute_with_acyclic_aux₂ C₁ B i).hom =
  (Ext_compute_with_acyclic_aux₂ C₂ B i).hom ≫
  (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op ⋙
      (_root_.homology_functor _ _ (-i)).op).map
      (bounded_homotopy_category.lift ((of' C₁).π ≫ of'_hom f) (of' C₂).π).out).unop :=
hom_single_iso_naturality _ _ _ _ _

def Ext_compute_with_acyclic_HomB
  (B : 𝓐) := (preadditive_yoneda.obj B).right_op.map_homological_complex (complex_shape.up ℤ) ⋙
  homological_complex.unop_functor.right_op

lemma Ext_compute_with_acyclic_is_quasi_iso_aux
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B))
  (i : ℤ) :
  is_quasi_iso ((homotopy_category.quotient _ _).map
    ((Ext_compute_with_acyclic_HomB B).map (of' C).π.out).unop) :=
begin
  let P := (of' C).replace,
  let π : P ⟶ of' C := (of' C).π,
  let HomB := (preadditive_yoneda.obj B).right_op.map_homological_complex (complex_shape.up ℤ) ⋙
    homological_complex.unop_functor.right_op,
  let fq := (homotopy_category.quotient _ _).map (HomB.map π.out).unop,
  apply is_quasi_iso_of_op,
  let f := homological_complex.op_functor.map (HomB.map (quot.out π)),
  have := cone_triangleₕ_mem_distinguished_triangles _ _ f,
  replace := is_quasi_iso_iff_is_acyclic _ this,
  dsimp [homological_complex.cone.triangleₕ] at this,
  erw this, clear this i,
  constructor,
  intro i, obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩,
  refine is_zero.of_iso _ (homology_iso _ i (i+1) (i+1+1) _ _),
  rotate, { dsimp, refl }, { dsimp, refl },
  apply exact.homology_is_zero _,
  dsimp only [homotopy_category.quotient, quotient.functor_obj_as, homological_complex.cone_d],
  have hπ : is_quasi_iso π, { dsimp [π], apply_instance },
  have := cone_triangleₕ_mem_distinguished_triangles _ _ π.out,
  replace := is_quasi_iso_iff_is_acyclic _ this,
  dsimp [homological_complex.cone.triangleₕ] at this,
  simp only [quotient_map_out] at this,
  replace := this.mp _,
  swap, { convert hπ using 1, generalize : P.val = X, cases X, refl, },
  haveI preaux : ((quotient 𝓐 (complex_shape.up ℤ)).obj (homological_complex.cone (quot.out π))).is_bounded_above,
  { constructor,
    obtain ⟨a, ha⟩ := is_bounded_above.cond ((quotient 𝓐 (complex_shape.up ℤ)).obj C),
    obtain ⟨b, hb⟩ := is_bounded_above.cond P.val,
    refine ⟨max a b, _⟩,
    intros k hk,
    refine category_theory.limits.is_zero.biprod _ _,
    { apply hb, refine (le_max_right _ _).trans (hk.trans (lt_add_one _).le) },
    { apply ha, exact (le_max_left _ _).trans hk, } },
  have aux := @map_is_acyclic_of_acyclic _ _ _ _ _ _ this B _,
  { replace := (@is_acyclic.cond _ _ _ _ _ _ aux (i+1)).of_iso (homology_iso _ i (i+1) (i+1+1) _ _).symm,
    rotate, { dsimp, refl }, { dsimp, refl },
    dsimp only [homotopy_category.quotient, quotient.functor_obj_as, homological_complex.cone_d,
      functor.map_homotopy_category_obj, functor.map_homological_complex_obj_d] at this,
    replace := exact_of_homology_is_zero this,
    let e := functor.map_biprod (preadditive_yoneda.obj B).right_op,
    refine preadditive.exact_of_iso_of_exact' _ _ _ _ (e _ _) (e _ _) (e _ _) _ _ this;
    dsimp only [e, functor.map_biprod_hom],
    all_goals
    { ext,
      { simp only [category.assoc, functor.right_op_map, homological_complex.cone.d, biprod.lift_fst,
          eq_self_iff_true, functor.map_homological_complex_obj_d, functor.right_op_map,
          homological_complex.X_eq_to_iso_refl, category.comp_id, dite_eq_ite, if_true,
          biprod.lift_fst, biprod.lift_desc, preadditive.comp_neg, comp_zero, add_zero],
        simp only [functor.map_homological_complex_obj_d, functor.right_op_map, functor.comp_map,
          biprod.lift_desc, preadditive.comp_neg, comp_zero, add_zero,
          ← op_comp, ← category_theory.functor.map_comp, biprod.lift_fst],
        simp only [biprod.desc_eq, comp_zero, add_zero, preadditive.comp_neg,
          category_theory.op_neg, functor.map_neg, op_comp, category_theory.functor.map_comp],
        refl },
      { simp only [category.assoc, functor.right_op_map, homological_complex.cone.d, biprod.lift_snd,
          eq_self_iff_true, functor.map_homological_complex_obj_d, functor.right_op_map,
          functor.map_homological_complex_map_f, homological_complex.X_eq_to_iso_refl,
          category.comp_id, dite_eq_ite, if_true, biprod.lift_snd, biprod.lift_desc],
        simp only [functor.map_homological_complex_obj_d, functor.right_op_map, functor.comp_map,
          biprod.lift_desc, preadditive.comp_neg, comp_zero, add_zero,
          ← op_comp, ← category_theory.functor.map_comp, biprod.lift_snd],
        simp only [biprod.desc_eq, op_add, functor.map_neg, functor.map_add, op_comp,
          category_theory.functor.map_comp],
        refl } } },
  { clear i, intros k i hi,
    let e := functor.map_biprod ((Ext' i).flip.obj B).right_op
      (P.val.as.X (k + 1)) ((of' C).val.as.X k),
    refine is_zero.of_iso (is_zero.unop _) e.symm.unop,
    refine category_theory.limits.is_zero.biprod _ _,
    { simp only [functor.right_op_obj, functor.flip_obj_obj, is_zero_op],
      exact acyclic_of_projective (P.val.as.X (k + 1)) B i hi, },
    { exact (hC k _ hi).op, }, },
end

def Ext_compute_with_acyclic_aux₃
  (B : 𝓐)
  (i : ℤ) :
  (((preadditive_yoneda.obj B).right_op.map_homological_complex _).obj C).unop.homology (-i) ⟶
  (((preadditive_yoneda.obj B).map_homological_complex (complex_shape.up ℤ).symm).obj
  ((of' C).replace).val.as.op).homology (-i) :=
by apply (homotopy_category.homology_functor Ab _ (-i)).map
  (((homotopy_category.quotient _ _).map
    ((Ext_compute_with_acyclic_HomB B).map (of' C).π.out).unop))

-- Are these two lemmas useful? Do we have them?
lemma functor.map_unop {𝓐 : Type*} [category 𝓐] {𝓑 : Type*}
  [category 𝓑] (F : 𝓐 ⥤ 𝓑) {a₁ a₂ : 𝓐ᵒᵖ}
  (f : a₁ ⟶ a₂) : F.map f.unop = (F.op.map f).unop :=
rfl

lemma functor.map_map' {𝓐 : Type*} [category 𝓐] {𝓑 : Type*}
  [category 𝓑] {𝓒 : Type*} [category 𝓒] (F : 𝓐 ⥤ 𝓑) (G : 𝓑 ⥤ 𝓒) {a₁ a₂ : 𝓐}
  (φ : a₁ ⟶ a₂) : G.map (F.map φ) = (F ⋙ G).map φ :=
rfl

namespace Ext_compute_with_acyclic_aux₃_naturality_helpers

variables (C₁ C₂ : cochain_complex 𝓐 ℤ)
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₁).is_bounded_above]
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₂).is_bounded_above]
  (B : 𝓐)
  (f : C₁ ⟶ C₂)
  (i : ℤ)

lemma helper₁ (h1 h2) :
  homology.lift ((unop
    (homological_complex.unop_functor.right_op.obj
    (((preadditive_yoneda.obj B).right_op.map_homological_complex
      (complex_shape.up ℤ)).obj C₁))).d_to (-i))
  ((unop (homological_complex.unop_functor.right_op.obj
    (((preadditive_yoneda.obj B).right_op.map_homological_complex
    (complex_shape.up ℤ)).obj C₁))).d_from (-i)) h1
  (kernel.ι ((unop (homological_complex.unop_functor.right_op.obj
    (((preadditive_yoneda.obj B).right_op.map_homological_complex
    (complex_shape.up ℤ)).obj C₂))).d_from (-i)) ≫
    (homological_complex.unop_functor.right_op.map
    (((preadditive_yoneda.obj B).right_op.map_homological_complex
    (complex_shape.up ℤ)).map f)).unop.f (-i) ≫ cokernel.π
    ((unop (homological_complex.unop_functor.right_op.obj
    (((preadditive_yoneda.obj B).right_op.map_homological_complex
    (complex_shape.up ℤ)).obj C₁))).d_to (-i))) h2 =
  kernel.lift _ (kernel.ι _ ≫ (preadditive_yoneda.obj B).map (f.f (-i)).op) begin
    rw category.assoc,
    have aux := ((((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op).map f)).unop.comm_from (-i),
    dsimp at aux,
    erw [aux, kernel.condition_assoc, zero_comp],
  end ≫
  homology.π' _ _ _ :=
begin
  apply homology.hom_to_ext,
  rw [category.assoc, homology.π'_ι, kernel.lift_ι_assoc,
    homology.lift_ι],
  refl,
end

lemma helper₂ (h1 h2) :
  homology.lift ((unop ((Ext_compute_with_acyclic_HomB B).obj (of' C₂).replace.val.as)).d_to (-i))
  ((unop ((Ext_compute_with_acyclic_HomB B).obj (of' C₂).replace.val.as)).d_from (-i))
  h1
  (kernel.ι ((unop ((Ext_compute_with_acyclic_HomB B).obj (of' C₂).val.as)).d_from (-i)) ≫
     ((Ext_compute_with_acyclic_HomB B).map (quot.out (of' C₂).π)).unop.f (-i) ≫
       cokernel.π ((unop ((Ext_compute_with_acyclic_HomB B).obj (of' C₂).replace.val.as)).d_to (-i)))
  h2 =
  kernel.lift _ (kernel.ι _ ≫ begin
    apply homological_complex.hom.f,
    exact (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op).map (of' C₂).π.out).unop,
  end) begin
    rw category.assoc,
    have := (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op).map (of' C₂).π.out).unop.comm_from (-i),
    erw [this, kernel.condition_assoc, zero_comp],
  end ≫ homology.π' _ _ _ :=
begin
  apply homology.hom_to_ext,
  simp only [homology.lift_ι, category.assoc, homology.π'_ι, kernel.lift_ι_assoc],
  refl,
end

end Ext_compute_with_acyclic_aux₃_naturality_helpers

lemma Ext_compute_with_acyclic_aux₃_naturality
  (C₁ C₂ : cochain_complex 𝓐 ℤ)
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₁).is_bounded_above]
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₂).is_bounded_above]
  (B : 𝓐)
  (f : C₁ ⟶ C₂)
  (i : ℤ) :
  (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
    homological_complex.unop_functor.right_op ⋙ (_root_.homology_functor _ _ (-i)).op).map f).unop
    ≫ Ext_compute_with_acyclic_aux₃ C₁ B i =
  Ext_compute_with_acyclic_aux₃ C₂ B i ≫
  (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op ⋙
      (_root_.homology_functor _ _ (-i)).op).map
      (bounded_homotopy_category.lift ((of' C₁).π ≫ of'_hom f) (of' C₂).π).out).unop :=
begin
  dsimp only [Ext_compute_with_acyclic_aux₃, functor.comp_map,
    _root_.homology_functor, functor.op, homological_complex.hom.sq_from,
    homological_complex.hom.sq_to, homotopy_category.quotient,
    homotopy_category.homology_functor, quotient.functor,
    category_theory.quotient.lift, quot.lift_on, quiver.hom.unop_op],
  simp_rw homology.map_eq_desc'_lift_left,
  apply homology.hom_from_ext,
  simp only [category.assoc, homology.π'_desc'_assoc],
  slice_rhs 1 2
  { erw homology.π'_desc' },
  dsimp only [arrow.hom_mk_left],
  rw Ext_compute_with_acyclic_aux₃_naturality_helpers.helper₁,
  conv_rhs { rw Ext_compute_with_acyclic_aux₃_naturality_helpers.helper₂ },
  simp only [category.assoc],
  slice_lhs 2 3
  { erw homology.π'_desc' },
  slice_rhs 2 3
  { erw homology.π'_desc' },
  apply homology.hom_to_ext,
  slice_lhs 2 3
  { erw homology.lift_ι },
  slice_rhs 2 3
  { erw homology.lift_ι },
  slice_lhs 1 2
  { erw kernel.lift_ι },
  slice_rhs 1 2
  { erw kernel.lift_ι },
  simp only [category.assoc],
  dsimp only [Ext_compute_with_acyclic_HomB, functor.comp_map],
  change _ ≫ (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op).map f).unop.f _ ≫ _ = _,
  slice_lhs 2 3
  { simp only [← homological_complex.comp_f, ← unop_comp],
    simp only [functor.comp_map, ← functor.map_comp] },
  slice_rhs 2 3
  { simp only [← homological_complex.comp_f, ← unop_comp, ← functor.map_comp] },
  apply homotopy.kernel_ι_comp_comp_cokernel_π_of_homotopy,
  apply homotopy.homotopy_unop_functor_right_op_map_unop_of_homotopy,
  apply functor.map_homotopy,
  suffices : (lift ((of' C₁).π ≫ of'_hom f) (of' C₂).π) ≫ (of' C₂).π =
    (of' C₁).π ≫ of'_hom f,
  { apply homotopy_category.homotopy_of_eq,
    convert this.symm,
    { simpa only [functor.map_comp, quotient_map_out], },
    { simpa only [functor.map_comp, quotient_map_out], } },
  simp,
end


lemma Ext_compute_with_acyclic_aux₃_is_iso
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B))
  (i : ℤ) : is_iso (Ext_compute_with_acyclic_aux₃ C B i) :=
begin
  haveI := Ext_compute_with_acyclic_is_quasi_iso_aux C B hC i,
  apply is_quasi_iso.cond,
end

def Ext_compute_with_acyclic
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B))
  (i : ℤ) :
  ((Ext i).obj (op $ of' C)).obj ((single _ 0).obj B) ≅
  (((preadditive_yoneda.obj B).right_op.map_homological_complex _).obj C).unop.homology (-i) :=
Ext_compute_with_acyclic_aux₁ C B i ≪≫
Ext_compute_with_acyclic_aux₂ _ _ _ ≪≫
begin
  haveI := Ext_compute_with_acyclic_aux₃_is_iso C B hC i,
  exact (as_iso (Ext_compute_with_acyclic_aux₃ C B i)).symm,
end

/-
def homological_complex.single_iso (B : 𝓐) {i j : ℤ} (h : j = i) :
  ((homological_complex.single _ (complex_shape.up ℤ) i).obj B).X j ≅ B :=
eq_to_iso (if_pos h)

/-- The morphism in `Ab` which eats a morphism of complexes `C ⟶ B[-i]`
  and returns an element of Extⁱ(C,B[0]). -/
def Ext_compute_with_acyclic_inv_eq_aux (B) (i) :
  AddCommGroup.of (C ⟶ (homological_complex.single _ _ (-i)).obj B) ⟶
  ((Ext i).obj (op (of' C))).obj ((single 𝓐 0).obj B) :=
{ to_fun := λ f, (of' C).π ≫ begin
    refine (homotopy_category.quotient _ _).map _,
    refine _ ≫ (homological_complex.single_shift _ _).inv.app _,
    refine (f : C ⟶ (homological_complex.single 𝓐 (complex_shape.up ℤ) (-i)).obj B) ≫ _,
    refine eq_to_hom _,
    simp,
  end,
  map_zero' := begin
    simp only [zero_comp, functor.map_zero, comp_zero],
  end,
  map_add' := begin
    intros,
    simp only [preadditive.add_comp, functor.map_add, preadditive.comp_add],
  end }

lemma iso_equiv_inv_apply_eq_zero_cancel
  {A B C : AddCommGroup} {a : A} {f : A ⟶ B} {e : C ≅ B}
  (h : (f ≫ e.inv) a = 0) : f a = 0 :=
begin
  rw comp_apply at h,
  apply_fun e.hom at h,
  simpa using h,
end

-- Note: in the application of the below, j = -i
/-- The construction which given something in the kernel of `(Cⱼ ⟶ B) ⟶ (Cⱼ-₁ ⟶ B)`
  constructs a morphism of complexes from C to the "skyscraper complex" B[j]. -/
def kernel_yoneda_complex_to_morphism_to_single (B : 𝓐) (j : ℤ) :
-- we're going from the kernel of `(C.X j ⟶ B) ⟶ (C.X_prev j ⟶ B)` (it's actually `C.symm.X_next`)
kernel ((((preadditive_yoneda.obj B).map_homological_complex _).obj
  (homological_complex.op C)).d_from j)
  -- to the additive group of homs
  ⟶ AddCommGroup.of (
  -- from C to B j
  C ⟶ (homological_complex.single 𝓐 (complex_shape.up ℤ) j).obj B) :=
{ to_fun := λ f, { f := λ k,
  if hk : k = j then
    (eq_to_hom (by rw hk) : C.X k ⟶ C.X j) ≫
    (kernel.ι ((((preadditive_yoneda.obj B).map_homological_complex _).obj
                (homological_complex.op C)).d_from j) f : C.X j ⟶ B) ≫
    (homological_complex.single_obj_X_self 𝓐 (complex_shape.up ℤ) j B).inv ≫
    eq_to_hom (by rw hk)
  else 0,
    comm' := λ i k, begin
      split_ifs with hij hkj hkj,
      { subst hij, subst hkj, simp {contextual := tt}, },
      { simp only [homological_complex.single_obj_d, comp_zero, eq_self_iff_true,
          implies_true_iff] },
      { subst hkj,
        set g := ((kernel.ι ((((preadditive_yoneda.obj B).map_homological_complex
                            (complex_shape.up ℤ).symm).obj
                  (homological_complex.op C)).d_from k)) f) with hg,
        simp only [complex_shape.up_rel, zero_comp, eq_to_hom_refl,
          homological_complex.single_obj_X_self_inv, category.comp_id, category.id_comp],
        rintro hik, clear hij,
        have := kernel.condition ((((preadditive_yoneda.obj B).map_homological_complex _).obj
          (homological_complex.op C)).d_from k),
        replace this := congr_hom this f,
        rw [comp_apply, ← hg, AddCommGroup.zero_apply] at this,
        rw ← category.assoc,
        symmetry,
        convert zero_comp,
        have foo : (complex_shape.up ℤ).symm.rel k i := hik,
        rw homological_complex.d_from_eq _ foo at this,
        exact iso_equiv_inv_apply_eq_zero_cancel this, },
      { simp only [zero_comp, comp_zero, eq_self_iff_true, implies_true_iff]},
    end },
  map_zero' := by {simp only [map_zero, homological_complex.single_obj_X_self_inv,
    eq_to_hom_trans, zero_comp, comp_zero, dite_eq_ite, if_t_t], refl },
  map_add' := by { intros, ext, simp only [map_add, homological_complex.single_obj_X_self_inv,
    eq_to_hom_trans, preadditive.add_comp, preadditive.comp_add, homological_complex.add_f_apply],
    split_ifs,
    { refl },
    { refl },
    { exact (add_zero _).symm, } } }

lemma Ext_compute_with_acylic_inv_eq (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B))
  (i : ℤ) :
  (Ext_compute_with_acyclic _ B hC i).inv =
  homology.desc' _ _ _
  ( kernel_yoneda_complex_to_morphism_to_single C B (-i) ≫
    Ext_compute_with_acyclic_inv_eq_aux C B i)
admit := admit

-- Replacing some `End` with `cend` fixes my bracket pair colorizer!
-- notation `cend` := category_theory.End

-/

lemma Ext_compute_with_acyclic_naturality (C₁ C₂ : cochain_complex 𝓐 ℤ)
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₁).is_bounded_above]
  [((quotient 𝓐 (complex_shape.up ℤ)).obj C₂).is_bounded_above]
  (B : 𝓐)
  (hC₁ : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C₁.X k)).obj B))
  (hC₂ : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C₂.X k)).obj B))
  (f : C₁ ⟶ C₂)
  (i : ℤ) :
  ((Ext i).flip.obj ((single _ 0).obj B)).map (quiver.hom.op $ of'_hom f) ≫
    (Ext_compute_with_acyclic C₁ B hC₁ i).hom =
  (Ext_compute_with_acyclic C₂ B hC₂ i).hom ≫
    (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op ⋙
      (_root_.homology_functor _ _ (-i)).op).map f).unop :=
begin
  dsimp only [Ext_compute_with_acyclic, iso.trans_hom],
  slice_lhs 1 2
  { erw Ext_compute_with_acyclic_aux₁_naturality },
  slice_lhs 2 3
  { rw Ext_compute_with_acyclic_aux₂_naturality },
  simp only [category.assoc],
  congr' 2,
  dsimp only [iso.symm_hom, as_iso_inv],
  rw [is_iso.eq_inv_comp, ← category.assoc, is_iso.comp_inv_eq],
  symmetry,
  apply Ext_compute_with_acyclic_aux₃_naturality,
end
