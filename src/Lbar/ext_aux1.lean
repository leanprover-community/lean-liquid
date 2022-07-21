import Lbar.ext_preamble

noncomputable theory

universes u v

open opposite category_theory category_theory.limits
open_locale nnreal zero_object

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

open bounded_homotopy_category

variables (BD : breen_deligne.data)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

def ExtQprime_iso_aux_system_obj_aux' (X : Profinite.{u}) :
  Ab.ulift.{u+1}.obj
    ((forget₂ SemiNormedGroup Ab).obj
      (SemiNormedGroup.Completion.obj ((SemiNormedGroup.LocallyConstant.obj V).obj (op X)))) ≅
  (forget₂ SemiNormedGroup.{u+1} Ab.{u+1}).obj
    (SemiNormedGroup.Completion.obj
      ((SemiNormedGroup.LocallyConstant.obj (SemiNormedGroup.ulift.{u+1}.obj V)).obj (op X))) :=
begin
  refine add_equiv.to_AddCommGroup_iso _,
  refine add_equiv.ulift.trans _,
  refine add_equiv.mk _ _ _ _ _,
  { refine normed_group_hom.completion _,
    refine locally_constant.map_hom _,
    refine { bound' := ⟨1, λ v, _⟩, .. add_equiv.ulift.symm },
    rw one_mul, exact le_rfl },
  { refine uniform_space.completion.map _,
    refine locally_constant.map_hom _,
    refine { bound' := ⟨1, λ v, _⟩, .. add_equiv.ulift },
    rw one_mul, exact le_rfl },
  { erw [function.left_inverse_iff_comp, uniform_space.completion.map_comp],
    { have : ulift.down.{u+1} ∘ ulift.up.{u+1} = (id : V → V) := rfl,
      erw [locally_constant.map_comp, this, locally_constant.map_id, uniform_space.completion.map_id] },
    { apply normed_group_hom.uniform_continuous, },
    { apply normed_group_hom.uniform_continuous, } },
  { erw [function.right_inverse_iff_comp, uniform_space.completion.map_comp],
    { have : ulift.up.{u+1 u} ∘ ulift.down.{u+1} = @id (ulift V) := by { ext v, refl },
      erw [locally_constant.map_comp, this, locally_constant.map_id, uniform_space.completion.map_id] },
    { apply normed_group_hom.uniform_continuous, },
    { apply normed_group_hom.uniform_continuous, } },
  { intros x y, apply map_add, }
end
.

attribute [simps] equiv.ulift add_equiv.ulift

lemma SemiNormedGroup.forget₂_Ab_map {V W : SemiNormedGroup} (f : V ⟶ W) :
  (forget₂ SemiNormedGroup Ab).map f = f.to_add_monoid_hom :=
rfl

lemma SemiNormedGroup.forget₂_Ab_obj (V : SemiNormedGroup) :
  (forget₂ SemiNormedGroup Ab).obj V = AddCommGroup.of V :=
rfl

set_option pp.universes true

--jmc: is this helpful??
@[reassoc]
lemma ExtQprime_iso_aux_system_obj_aux'_natural (X Y : Profinite.{u}) (f : X ⟶ Y) :
  (ExtQprime_iso_aux_system_obj_aux' V Y).hom ≫
    (forget₂ _ _).map (SemiNormedGroup.Completion.map ((SemiNormedGroup.LocallyConstant.obj _).map f.op)) =
    Ab.ulift.map ((forget₂ _ _).map (SemiNormedGroup.Completion.map ((SemiNormedGroup.LocallyConstant.obj _).map f.op))) ≫
 (ExtQprime_iso_aux_system_obj_aux' V X).hom :=
begin
  ext1 ⟨φ⟩, simp only [comp_apply],
  dsimp only [ExtQprime_iso_aux_system_obj_aux', add_equiv.to_AddCommGroup_iso,
    add_equiv.trans_apply, add_equiv.coe_to_add_monoid_hom, add_equiv.coe_mk,
    Ab.ulift_map_apply,
    SemiNormedGroup.forget₂_Ab_map, SemiNormedGroup.forget₂_Ab_obj,
    AddCommGroup.coe_of],
  apply uniform_space.completion.induction_on φ; clear φ,
  { refine @is_closed_eq _ _ _ _ (id _) _ _ _ _,
    { dsimp [SemiNormedGroup.Completion_obj, SemiNormedGroup.LocallyConstant_obj_obj],
      apply_instance },
    { apply uniform_space.completion.continuous_map.comp uniform_space.completion.continuous_map },
    { apply uniform_space.completion.continuous_map.comp,
      dsimp only [Ab.ulift, add_monoid_hom.coe_mk, add_equiv.ulift_apply,
        equiv.to_fun_as_coe, equiv.ulift_apply],
      apply uniform_space.completion.continuous_map } },
  { intros φ,
    dsimp only [Ab.ulift, add_monoid_hom.coe_mk, add_equiv.ulift_apply,
      equiv.to_fun_as_coe, equiv.ulift_apply,
      SemiNormedGroup.LocallyConstant_obj_map,
      SemiNormedGroup.Completion_map],
    erw [normed_group_hom.completion_coe, normed_group_hom.completion_coe,
      normed_group_hom.completion_coe, normed_group_hom.completion_coe],
    congr' 1,
    dsimp only [locally_constant.comap_hom_apply, locally_constant.map_hom_apply],
    erw [locally_constant.comap_map],
    exact f.continuous, }
end
.

open category_theory.preadditive

lemma FreeAb_naturality_helper {C 𝓐 : Type*} [category C] [category 𝓐] [preadditive 𝓐]
  (F G : FreeAb C ⥤ 𝓐) [F.additive] [G.additive]
  (η : ∀ X : FreeAb C, F.obj X ⟶ G.obj X)
  (hη : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map ((FreeAb.of_functor _).map f) ≫ η _ = η _ ≫ G.map ((FreeAb.of_functor _).map f))
  {X Y : FreeAb C} (f : X ⟶ Y) :
  F.map f ≫ η Y = η X ≫ G.map f :=
begin
  change right_comp _ (η Y) (F.map_add_hom f) = left_comp _ (η X) (G.map_add_hom f),
  rw [← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_apply], congr' 1, clear f,
  ext1 f, cases X, cases Y, exact hη f,
end

lemma ExtQprime_iso_aux_system_obj_aux_aux (X Y : Profinite.{u}) (f : X ⟶ Y) :
  (LCC_iso_Cond_of_top_ab.{u} V).inv.app (op.{u+2} Y) ≫
  (forget₂.{u+1 u+1 u u u} SemiNormedGroup.{u} Ab.{u}).map
    (SemiNormedGroup.Completion.{u}.map
    ((SemiNormedGroup.LocallyConstant.{u u}.obj V).map f.op)) =
  (Condensed.of_top_ab.presheaf _).map f.op ≫
  (LCC_iso_Cond_of_top_ab V).inv.app (op X) :=
begin
  simp only [← nat_iso.app_inv, iso.inv_comp_eq],
  simp only [← category.assoc, iso.eq_comp_inv],
  ext1 t, dsimp [forget₂, has_forget₂.forget₂,
    LCC_iso_Cond_of_top_ab, LCC_iso_Cond_of_top_ab_add_equiv] at t ⊢,
  simp only [comp_apply, normed_group_hom.coe_to_add_monoid_hom,
    add_equiv.coe_to_add_monoid_hom, add_equiv.coe_mk],
  dsimp only [Condensed.of_top_ab.presheaf, add_monoid_hom.mk'_apply],
  ext x,
  simp only [continuous_map.comp_apply],
  apply uniform_space.completion.induction_on t; clear t,
  { refine is_closed_eq _ _,
    { have h1 : continuous (λ q : C(X,V), q x) := continuous_map.continuous_eval_const.{u u} x,
      have h2 : continuous (uniform_space.completion.extension.{u u}
        locally_constant.to_continuous_map.{u u}) := uniform_space.completion.continuous_extension,
      have h3 := (locally_constant.comap_hom.{u u u} f f.continuous).completion.continuous,
      refine (h1.comp h2).comp h3,
      apply_instance },
    { let t := _, change continuous t,
      have ht : t = _ ∘ uniform_space.completion.extension
        (locally_constant.to_continuous_map.{u u}),
      rotate 2,
      { intros q, exact q (f x) },
      { refl },
      rw ht, clear ht t,
      apply continuous.comp,
      exact continuous_map.continuous_eval_const.{u u} (f x),
      exact uniform_space.completion.continuous_extension.{u u} } },
  { intros a,
    simp only [normed_group_hom.completion_coe,
      locally_constant.comap_hom_apply, quiver.hom.unop_op],
    erw [uniform_space.completion.extension_coe],
    erw [uniform_space.completion.extension_coe],
    unfold locally_constant.comap,
    classical,
    erw dif_pos, refl,
    exact f.continuous,
    exact locally_constant.to_continuous_map_uniform_continuous.{u} Y ↥V,
    exact locally_constant.to_continuous_map_uniform_continuous.{u} X ↥V },
end

def ExtQprime_iso_aux_system_obj_aux :
  ((CLC (SemiNormedGroup.ulift.{u+1}.obj V)).right_op.map_FreeAb ⋙
         FreeAb.eval SemiNormedGroupᵒᵖ) ⋙
    (forget₂ SemiNormedGroup Ab).op ≅
  (freeCond.map_FreeAb ⋙ FreeAb.eval (Condensed.{u} Ab.{u+1})) ⋙
    (preadditive_yoneda.obj V.to_Cond).right_op :=
begin
  refine nat_iso.of_components _ _,
  { intro X,
    dsimp only [functor.comp_obj, functor.right_op, functor.op_obj, FreeAb.eval,
      functor.map_FreeAb],
    refine iso.op _,
    refine (preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab _ _) ≪≫ _,
    let e := (Condensed_Ab_to_presheaf.map_iso (Condensed_LCC_iso_of_top_ab V)).app (op X.as),
    refine e.symm ≪≫ (ExtQprime_iso_aux_system_obj_aux' V X.as), },
  { intros X Y f,
    apply FreeAb_naturality_helper, clear f X Y, intros X Y f,
    dsimp only [id.def, iso.trans_hom, iso.op_hom, op_comp, iso.symm_hom, functor.map_iso_inv,
      functor.comp_map, functor.right_op_map, functor.op_map, iso.app_inv,
      FreeAb.eval, functor.map_FreeAb, FreeAb.of_functor],
    simp only [category.assoc, ← op_comp], congr' 1,
    simp only [free_abelian_group.map_of_apply, free_abelian_group.lift.of, id.def,
      functor.right_op_map, quiver.hom.unop_op],
    erw ← preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab_natural'_assoc,
    congr' 1,
    dsimp [Condensed_LCC_iso_of_top_ab],
    erw ExtQprime_iso_aux_system_obj_aux'_natural,
    simp only [← category.assoc], congr' 1,
    rw ← Ab.ulift.map_comp,
    rw ExtQprime_iso_aux_system_obj_aux_aux,
    ext, refl }
end

/-- Hom(X,A) -/
def hom_complex_int (X : homological_complex (Condensed.{u} Ab.{u+1})
  (complex_shape.up ℤ)) (A : Condensed.{u} Ab.{u+1}) :
  homological_complex Ab.{u+1} (complex_shape.up ℤ).symm :=
(((preadditive_yoneda.obj A).map_homological_complex _).obj X.op)

def hom_complex_nat (X : homological_complex (Condensed.{u} Ab.{u+1})
  (complex_shape.down ℕ)) (A : Condensed.{u} Ab.{u+1}) :
  homological_complex Ab.{u+1} (complex_shape.down ℕ).symm :=
(((preadditive_yoneda.obj A).map_homological_complex _).obj X.op)

def embed_hom_complex_nat_iso (X : homological_complex (Condensed.{u} Ab.{u+1})
  (complex_shape.down ℕ)) (A : Condensed.{u} Ab.{u+1}) :
  hom_complex_int ((homological_complex.embed
    complex_shape.embedding.nat_down_int_up).obj X) A ≅
  (homological_complex.embed complex_shape.embedding.nat_up_int_down).obj
  (hom_complex_nat X A) :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| int.of_nat 0 := iso.refl _
| int.of_nat (i+1) := is_zero.iso (functor.map_is_zero _ (is_zero_zero _).op) (is_zero_zero _)
| -[1+i] := iso.refl _
end)
begin
  rintro i (j|(_|j)) (rfl : _ = _),
  { apply is_zero.eq_of_src,
    refine functor.map_is_zero _ _,
    dsimp, apply is_zero.op, exact is_zero_zero _ },
  { refine (category.id_comp _).trans (category.comp_id _).symm, },
  { refine (category.id_comp _).trans (category.comp_id _).symm, },
end

/-
lemma embed_hom_complex_nat_iso_homology_iso (X : homological_complex (Condensed.{u} Ab.{u+1})
  (complex_shape.down ℕ)) (A : Condensed.{u} Ab.{u+1}) (n : ℕ) :
  (homology_functor _ _ (-(n : ℤ))).map (embed_hom_complex_nat_iso X A).hom ≫
  (homological_complex.homology_embed_nat_iso _
    complex_shape.embedding.nat_up_int_down nat_up_int_down_c_iff
    n (-(n : ℤ)) (by { cases n; refl })).app _
  = _
-/

/-
-- OLD construction of ExtQprime_iso_aux_system_obj
begin
  refine (homology_functor _ _ (-n:ℤ)).map_iso _ ≪≫ _,
  { let C := ((preadditive_yoneda.obj V.to_Cond).right_op.map_homological_complex _).obj
      (((QprimeFP_nat r' BD κ M).obj c)),
    exact ((homological_complex.embed complex_shape.embedding.nat_up_int_down).obj C.unop), },
  { refine _ ≪≫ embed_unop.app (op (((preadditive_yoneda_obj V.to_Cond ⋙ forget₂ _ _).right_op.map_homological_complex
      (complex_shape.down ℕ)).obj ((QprimeFP_nat r' BD κ M).obj c))),
    dsimp,
    refine (homological_complex.unop_functor.right_op.map_iso _).unop,
    symmetry, refine (map_homological_complex_embed _).app _, },
  refine (homological_complex.homology_embed_nat_iso _
    complex_shape.embedding.nat_up_int_down nat_up_int_down_c_iff
    n (-n) (by { cases n; refl })).app _ ≪≫ (homology_functor _ _ _).map_iso _,
  refine hom_complex_QprimeFP_nat_iso_aux_system r' BD κ M V c
end
-/

def hom_complex_QprimeFP_nat_iso_aux_system (c : ℝ≥0) :
  hom_complex_nat.{u} ((QprimeFP_nat.{u} r' BD κ M).obj c) V.to_Cond ≅
  (aux_system.{u u+1} r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1 u}.obj V) κ).to_Ab.obj (op.{1} c) :=
begin
  refine _ ≪≫ forget₂_unop.app _,
  let φ : op (((preadditive_yoneda.obj V.to_Cond).right_op.map_homological_complex (complex_shape.down ℕ)).obj
  ((QprimeFP_nat r' BD κ M).obj c)) ≅ _ := _,
  refine homological_complex.unop_functor.map_iso φ,
  refine ((category_theory.nat_iso.map_homological_complex
    (ExtQprime_iso_aux_system_obj_aux V) _).app ((breen_deligne.FPsystem r' BD _ κ).obj c)).op,
end

def ExtQprime_iso_aux_system_obj (c : ℝ≥0) (n : ℕ) :
  ((Ext n).obj (op $ (QprimeFP r' BD κ M).obj c)).obj ((single _ 0).obj V.to_Cond) ≅
  ((aux_system r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ).to_AbH n).obj (op c) :=
Ext_compute_with_acyclic _ _ (ExtQprime_iso_aux_system_aux r' BD κ M V c) _ ≪≫
begin
  refine (homology_functor _ _ (-n:ℤ)).map_iso
    (embed_hom_complex_nat_iso _ _) ≪≫ _,
  refine (homological_complex.homology_embed_nat_iso _
    complex_shape.embedding.nat_up_int_down nat_up_int_down_c_iff
    n (-n) (by { cases n; refl })).app _ ≪≫ (homology_functor _ _ _).map_iso _,
  refine hom_complex_QprimeFP_nat_iso_aux_system r' BD κ M V c
end

attribute [reassoc] Ext_compute_with_acyclic_naturality

def cofan_point_iso_colimit {α : Type (u+1)}
  (X : α → bounded_homotopy_category (Condensed.{u} Ab.{u+1}))
  [bounded_homotopy_category.uniformly_bounded X] :
  (bounded_homotopy_category.cofan X).X ≅
  ∐ X :=
(bounded_homotopy_category.is_colimit_cofan X).cocone_point_unique_up_to_iso
  (colimit.is_colimit _)

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

instance sigma_Qprime_int_bounded_above :
  ((homotopy_category.quotient (Condensed Ab) (complex_shape.up ℤ)).obj
    (∐ λ (k : ulift ℕ), (QprimeFP_int r' BD κ M).obj (ι k))).is_bounded_above :=
begin
  refine ⟨⟨1, _⟩⟩,
  intros a ha,
  refine is_zero.of_iso _ (homotopy_category.coproduct_iso _ _),
  apply category_theory.is_zero_colimit,
  intro,
  exact chain_complex.bounded_by_one _ _ ha,
end
.

def coproduct_shift (A : Type u)
  [category.{v} A]
  [abelian A]
  [has_coproducts A]
  (X : ulift.{v} ℕ → bounded_homotopy_category A)
  [uniformly_bounded X]
  (e : X ⟶ (λ i, X (ulift.up $ ulift.down i + 1))) :
  ∐ X ⟶ ∐ X :=
begin
  apply sigma.desc,
  intros i,
  refine _ ≫ sigma.ι _ (ulift.up $ ulift.down i + 1),
  refine e _,
end


@[reassoc]
lemma Ext_coproduct_iso_naturality_shift
  (A : Type u)
  [category.{v} A]
  [abelian A]
  [enough_projectives A]
  [has_coproducts A]
  [AB4 A]
  (X : ulift.{v} ℕ → bounded_homotopy_category A)
  [uniformly_bounded X]
  (e : X ⟶ (λ i, X (ulift.up $ ulift.down i + 1)))
  (i : ℤ) (Y) :
  ((Ext i).map (coproduct_shift _ X e).op).app Y ≫
  (Ext_coproduct_iso X _ _).hom =
  (Ext_coproduct_iso _ _ _).hom ≫
  pi.lift (λ j, pi.π _ (ulift.up (ulift.down j + 1)) ≫
    ((Ext i).map (e _).op).app Y) :=
begin
  dsimp only [Ext_coproduct_iso, Ext, Ext0, Ext_iso, functor.comp_map, whiskering_left,
    whisker_left, iso.trans_hom, functor.map_iso, preadditive_yoneda_coproduct_iso,
    functor.flip, pi_iso, as_iso, preadditive_yoneda_coproduct_to_product],
  simp only [category.assoc],
  simp only [quiver.hom.unop_op, iso.op_hom, replacement_iso_hom, iso.op_inv,
    replacement_iso_inv, iso.symm_mk],
  apply limit.hom_ext,
  intros j,
  simp only [category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π_assoc],
  simp only [← functor.map_comp, ← op_comp],
  congr' 2,
  simp only [category.assoc],
  apply lift_ext (∐ X).π, swap, apply_instance,
  dsimp [quiver.hom.unop_op],
  simp only [category.assoc, lift_lifts, lift_lifts_assoc],
  dsimp [uniform_π, coproduct_shift],
  simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, colimit.ι_desc,
    lift_lifts_assoc],
end
