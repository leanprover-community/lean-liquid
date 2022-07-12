import Lbar.ext_preamble

noncomputable theory

universes u

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
  { intros x y, apply normed_group_hom.map_add, }
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

-- this needs to be functorial in `c`
def ExtQprime_iso_aux_system_obj (c : ℝ≥0) (n : ℕ) :
  ((Ext n).obj (op $ (QprimeFP r' BD κ M).obj c)).obj ((single _ 0).obj V.to_Cond) ≅
  ((aux_system r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ).to_AbH n).obj (op c) :=
Ext_compute_with_acyclic _ _ (ExtQprime_iso_aux_system_aux r' BD κ M V c) _ ≪≫
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
    n (-n) _).app _ ≪≫ _,
  { cases n; refl },
  refine (homology_functor _ _ n).map_iso _,
  refine _ ≪≫ forget₂_unop.app _,
  let φ : op (((preadditive_yoneda.obj V.to_Cond).right_op.map_homological_complex (complex_shape.down ℕ)).obj
  ((QprimeFP_nat r' BD κ M).obj c)) ≅ _ := _,
  refine homological_complex.unop_functor.map_iso φ,
  refine ((category_theory.nat_iso.map_homological_complex
    (ExtQprime_iso_aux_system_obj_aux V) _).app ((breen_deligne.FPsystem r' BD _ κ).obj c)).op,
end

attribute [reassoc] Ext_compute_with_acyclic_naturality
