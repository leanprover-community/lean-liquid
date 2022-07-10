import for_mathlib.derived.K_projective
import for_mathlib.homological_complex_op
import for_mathlib.homology_iso_Ab
import for_mathlib.hom_single_iso

noncomputable theory

universes v u

open category_theory category_theory.limits category_theory.preadditive

variables {C : Type u} {ι : Type*} [category.{v} C] [abelian C] {c : complex_shape ι}

namespace bounded_homotopy_category

open hom_single_iso_setup opposite

lemma aux₁_naturality_snd_var
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ) (f : B₁ ⟶ B₂) :
  (aux₁ P B₁ i).hom ≫
  (homology_functor AddCommGroup (complex_shape.up ℤ).symm i).map
    ((nat_trans.map_homological_complex (preadditive_yoneda.map f)
    (complex_shape.up ℤ).symm).app P.val.as.op) =
  map_hom_complex_homology _ _ f _ _ ≫ (aux₁ P B₂ i).hom :=
begin
  rw [← iso.comp_inv_eq],
  ext : 2,
  dsimp only [aux₁, iso.symm_hom, iso.symm_inv, homology_iso', homology.map_iso],
  simp only [category.assoc],
  rw [homology.map_eq_desc'_lift_left, homology.π'_desc'_assoc,
    homology.map_eq_lift_desc'_left, homology.lift_ι,
    map_hom_complex_homology,
    homology.map_eq_lift_desc'_left, homology.lift_ι, homology.π'_desc'],
  dsimp only [arrow.hom_mk_left, map_hom_complex',
    nat_trans.map_homological_complex_app_f, homology_functor_map],
  let t : _ := _, show _ ≫ _ ≫ t = _,
  have ht : t = homology.ι _ _ _ ≫
    cokernel.map _ _ (homological_complex.X_prev_iso _ _).hom (𝟙 _) _,
  rotate 2, { dsimp, refl }, { rw [category.comp_id], apply homological_complex.d_to_eq },
  { ext1, erw [homology.π'_ι_assoc, homology.π'_desc', cokernel.π_desc], refl, },
  rw [ht, homology.map_eq_lift_desc'_right, homology.lift_ι_assoc], clear ht t,
  let t : _ := _, show t ≫ _ = _,
  have ht : t = kernel.map _ _ (𝟙 _) (homological_complex.X_next_iso _ _).inv _ ≫
    homology.π' _ _ _,
  rotate 2, { dsimp, apply sub_add_cancel },
  { rw [category.id_comp], symmetry, apply homological_complex.d_from_eq },
  { ext1, erw [homology.lift_ι, category.assoc, homology.π'_ι, kernel.lift_ι_assoc], refl },
  rw [ht, category.assoc, homology.π'_desc'_assoc, category.assoc, category.assoc], clear ht t,
  rw [kernel.lift_ι_assoc, cokernel.π_desc],
  simp only [category.assoc, category.id_comp], refl,
end

lemma aux₂_naturality_snd_var
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ) (f : B₁ ⟶ B₂) :
  (aux₂ P B₁ i).inv ≫ P.map_hom_complex_homology i f _ (homological_complex.d_comp_d _ _ _ _) =
  AddCommGroup.homology_map
    (homological_complex.d_comp_d _ _ _ _)
    (homological_complex.d_comp_d _ _ _ _)
    (commsq.of_eq $ ((map_hom_complex' _ f).comm _ _).symm)
    (commsq.of_eq $ ((map_hom_complex' _ f).comm _ _).symm) ≫ (aux₂ P B₂ i).inv :=
begin
  dsimp only [aux₂, map_hom_complex_homology],
  rw ← AddCommGroup.homology_iso_inv_homology_map,
  congr' 1,
  dsimp only [homology.map'],
  erw ← has_homology.homology_map_eq',
  congr',
end
.

lemma quotient_add_group.lift_mk''
  {G H : Type*} [add_group G] [add_group H] (N : add_subgroup G) [N.normal]
  {φ : G →+ H} (HN : ∀ (x : G), x ∈ N → φ x = 0) (g : G) :
  (quotient_add_group.lift N φ HN) (quotient_add_group.mk' N g) = φ g :=
quotient_add_group.lift_mk' _ _ _

attribute [elementwise] iso.inv_hom_id

lemma _root_.AddCommGroup.has_homology_ι_eq {A B C : AddCommGroup} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  (AddCommGroup.has_homology f g w).ι =
  (AddCommGroup.of_hom $ quotient_add_group.lift _ ((quotient_add_group.mk' f.range).comp g.ker.subtype)
      begin
        rintro x ⟨a, ha⟩,
        simp only [add_monoid_hom.comp_apply, quotient_add_group.coe_mk', quotient_add_group.eq_zero_iff],
        exact ⟨a, ha⟩,
      end) ≫
    (AddCommGroup.cokernel_iso_range_quotient _).inv :=
begin
  dsimp only [AddCommGroup.has_homology, AddCommGroup.of_hom],
  ext x,
  apply_fun (AddCommGroup.cokernel_iso_range_quotient f).hom,
  { simp only [add_monoid_hom.comp_apply, comp_apply, quotient_add_group.lift_mk'',
      AddCommGroup.cokernel_π_cokernel_iso_range_quotient_hom_apply,
      category_theory.iso.inv_hom_id_apply] },
  { erw [← AddCommGroup.mono_iff_injective], apply_instance },
end
.

lemma _root_.add_monoid_hom.lift_of_surjective_apply {A B C : Type*}
  [add_comm_group A] [add_comm_group B] [add_comm_group C]
  (f : A →+ B) (hf : function.surjective f) (g : {g : A →+ C // f.ker ≤ g.ker}) (a : A) :
  add_monoid_hom.lift_of_surjective f hf g (f a) = g a :=
begin
  show g _ = g _,
  erw [← sub_eq_zero, ← g.val.map_sub, ← g.val.mem_ker],
  apply g.2,
  rw [f.mem_ker, f.map_sub, sub_eq_zero],
  apply function.surj_inv_eq
end

lemma _root_.add_equiv.symm_mk_apply {A B : Type*} [add_comm_group A] [add_comm_group B]
  (f : A → B) (g : B → A) (h1) (h2) (h3) (b : B) :
  add_equiv.symm ⟨f, g, h1, h2, h3⟩ b = g b := rfl

lemma _root_.add_monoid_hom.subtype_mk_apply {A B : Type*} [add_comm_group A] [add_comm_group B]
  (p : (A →+ B) → Prop) (f : A →+ B) (hf : p f) (a : A) :
  subtype.mk f hf a = f a := rfl

lemma homological_complex_hom_single_iso_natural_aux
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ)
  (f : B₁ ⟶ B₂)
  (φ : (add_monoid_hom.ker ((hom_complex P B₁).d i (i - 1)))) :
  ((map_hom_complex' P f).f i) φ ∈ add_monoid_hom.ker ((hom_complex P B₂).d i (i - 1)) :=
begin
  cases φ with φ hφ,
  rw [add_monoid_hom.mem_ker] at hφ ⊢,
  rw [← comp_apply, (map_hom_complex' P f).comm, comp_apply],
  erw [hφ, map_zero],
end
.

attribute [simps] eq_to_iso

lemma homological_complex_hom_single_iso_natural
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ)
  (f : B₁ ⟶ B₂)
  (φ : (add_monoid_hom.ker ((hom_complex P B₁).d i (i - 1)))) :
  homotopy_category.quotient_map_hom P.val.as ((homological_complex.single C _ i).obj B₁)
    (((homological_complex.hom_single_iso P.val.as B₁ i).symm) φ) ≫
  (single C i).map f =
  homotopy_category.quotient_map_hom P.val.as ((homological_complex.single C _ i).obj B₂)
    (((homological_complex.hom_single_iso P.val.as B₂ i).symm)
      ⟨(map_hom_complex' P f).f i φ, homological_complex_hom_single_iso_natural_aux P i f φ⟩) :=
begin
  dsimp only [homotopy_category.quotient_map_hom, add_monoid_hom.mk'_apply,
    single, homotopy_category.single, functor.comp_map],
  rw [← functor.map_comp], congr' 1,
  ext n,
  dsimp only [homological_complex.comp_f, homological_complex.hom_single_iso_symm_apply_f],
  split_ifs with hin, swap, { rw zero_comp },
  subst n,
  simp only [category.assoc], refine congr_arg2 _ rfl _,
  dsimp only [map_hom_complex', nat_trans.map_homological_complex_app_f,
    preadditive_yoneda_map_app_apply],
  simp only [category.assoc], refine congr_arg2 _ rfl _,
  dsimp only [homological_complex.single],
  rw [← category_theory.eq_to_iso_hom, ← iso.eq_inv_comp],
  exact dif_pos rfl,
end

lemma hom_single_iso_naturality_snd_var_good
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ)
  (f : B₁ ⟶ B₂) :
  (hom_single_iso P B₁ i).hom ≫
  (homology_functor _ _ i).map (nat_trans.app (nat_trans.map_homological_complex
    (preadditive_yoneda.map f) _) _) =
  (preadditive_yoneda.map $ (single C i).map f).app (op P) ≫ (hom_single_iso P B₂ i).hom :=
begin
  dsimp only [hom_single_iso, iso.trans_hom, iso.symm_hom, functor.comp_map, functor.op_map,
    functor.right_op_map, quiver.hom.unop_op],
  simp only [category.assoc],
  rw aux₁_naturality_snd_var,
  simp_rw ← category.assoc, congr' 1, simp_rw category.assoc,
  rw aux₂_naturality_snd_var,
  simp_rw ← category.assoc, congr' 1,
  rw [← iso.eq_inv_comp],
  apply (AddCommGroup.has_homology _ _ _).ext_ι,
  apply (AddCommGroup.has_homology _ _ _).ext_π,
  rotate, { apply homological_complex.d_comp_d }, { apply homological_complex.d_comp_d },
  rw [AddCommGroup.homology_map, has_homology.map_ι, has_homology.π_comp_desc],
  dsimp only [map_hom_complex', nat_trans.map_homological_complex_app_f,
    add_equiv_iso_AddCommGroup_iso],
  simp only [AddCommGroup.has_homology_ι_eq, ← category.assoc],
  rw [iso.eq_comp_inv],
  dsimp only [AddCommGroup.has_homology],
  simp only [category.assoc],
  rw [← iso.inv_comp_eq],
  ext1 φ,
  simp only [category_theory.comp_apply, AddCommGroup.kernel_iso_ker_inv_comp_ι_apply,
    AddCommGroup.cokernel_π_cokernel_iso_range_quotient_hom_apply,
    AddCommGroup.of_hom, add_equiv.to_AddCommGroup_iso, add_equiv.coe_to_add_monoid_hom],
  dsimp only [aux₃, preadditive_yoneda_map_app_apply],
  dsimp only [add_equiv.surjective_congr, add_equiv.coe_mk, add_equiv.symm_mk_apply],
  rw [add_monoid_hom.lift_of_surjective_apply, add_monoid_hom.subtype_mk_apply],
  dsimp only [add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom],
  erw [homological_complex_hom_single_iso_natural P i f φ],
  rw [add_monoid_hom.lift_of_surjective_apply, add_monoid_hom.subtype_mk_apply],
  dsimp only [add_monoid_hom.comp_apply, add_equiv.coe_to_add_monoid_hom],
  rw [quotient_add_group.lift_mk'', add_equiv.apply_symm_apply, add_monoid_hom.comp_apply],
  refl,
end

lemma hom_single_iso_naturality_snd_var
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ)
  (f : B₁ ⟶ B₂) (x : P ⟶ (single C i).obj B₁) :
  ((homology_functor _ _ i).map
    ((nat_trans.map_homological_complex (preadditive_yoneda.map f) _).app P.val.as.op))
      ((hom_single_iso P B₁ i).hom x) = ((hom_single_iso P B₂ i).hom (x ≫ (single C i).map f)) :=
begin
  have := hom_single_iso_naturality_snd_var_good P i f,
  apply_fun (λ e, e x) at this,
  exact this
end

end bounded_homotopy_category
