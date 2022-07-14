import Lbar.ext_aux1

noncomputable theory

universes v u u'

open opposite category_theory category_theory.limits category_theory.preadditive
open_locale nnreal zero_object

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (r < r')] [fact (r < 1)]

section

open bounded_homotopy_category

variables (BD : breen_deligne.data)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

set_option pp.universes true

lemma QprimeFP_map (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) :
  (QprimeFP r' BD κ M).map h = of'_hom ((QprimeFP_int r' BD κ _).map h) := rfl

variables [fact (0 < r')] [fact (r' < 1)]

@[reassoc]
lemma massive_aux₁ (X Y : Profinite.{u}) (f : X ⟶ Y) :
  (preadditive_yoneda.{u+1 u+2}.obj V.to_Cond).map (freeCond.{u}.map f).op ≫
  (preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab.{u} V.to_Cond X).hom =
  (preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab.{u} V.to_Cond Y).hom ≫
  V.to_Cond.val.map f.op :=
sorry

lemma add_equiv.mk_symm {A B : Type*} [add_comm_group A] [add_comm_group B]
  (f : A →+ B) (g : B →+ A) (h1 h2 h3) :
  (add_equiv.mk f g h1 h2 h3).symm =
  add_equiv.mk g f h2 h1 (by { intros x y, apply h1.injective, rw [h3, h2, h2, h2] }) := rfl

lemma add_equiv.mk_symm_apply {A B : Type*} [add_comm_group A] [add_comm_group B]
  (f : A →+ B) (g : B →+ A) (h1 h2 h3) (x : B) :
  (add_equiv.mk f g h1 h2 h3).symm x = g x := rfl

lemma locally_constant.comap_hom_map_hom {X Y V W : Type*}
  [topological_space X] [compact_space X]
  [topological_space Y] [compact_space Y]
  [semi_normed_group V] [semi_normed_group W]
  (f : X → Y) (hf : continuous f) (g : normed_group_hom V W) (φ : locally_constant Y V) :
  locally_constant.comap_hom f hf (locally_constant.map_hom g φ) =
  ((locally_constant.map_hom g) ∘ (locally_constant.comap_hom f hf)) φ :=
begin
  dsimp only [locally_constant.comap_hom_apply, locally_constant.map_hom_apply, function.comp],
  rw locally_constant.comap_map,
  exact hf
end

lemma massive_aux (X Y : Profinite.{u}) (f : X ⟶ Y) :
  (preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab.{u} V.to_Cond Y).hom ≫
      Ab.ulift.{u+1 u}.map ((LCC_iso_Cond_of_top_ab.{u} V).inv.app (op.{u+2} Y)) ≫
        (ExtQprime_iso_aux_system_obj_aux'.{u} V Y).hom ≫
          (forget₂.{u+2 u+2 u+1 u+1 u+1} SemiNormedGroup.{u+1} Ab.{u+1}).map
            ((FreeAb.eval.{u+1 u+2} SemiNormedGroup.{u+1}ᵒᵖ).map
              ((CLC.{u+1 u} (SemiNormedGroup.ulift.{u+1 u}.obj V)).right_op.map_FreeAb.map
                  ((FreeAb.of_functor.{u+1 u} Profinite.{u}).map f))).unop =
    (preadditive_yoneda.{u+1 u+2}.obj V.to_Cond).map
        ((FreeAb.eval.{u+1 u+2} (Condensed.{u u+1 u+2} Ab.{u+1})).map
          (freeCond.{u}.map_FreeAb.map ((FreeAb.of_functor.{u+1 u} Profinite.{u}).map f))).op ≫
      (preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab.{u} V.to_Cond X).hom ≫
        Ab.ulift.{u+1 u}.map ((LCC_iso_Cond_of_top_ab.{u} V).inv.app (op.{u+2} X)) ≫
          (ExtQprime_iso_aux_system_obj_aux'.{u} V X).hom :=
begin
  dsimp only [functor.map_FreeAb, FreeAb.of_functor, FreeAb.eval],
  simp only [free_abelian_group.map_of_apply, free_abelian_group.lift.of, id],
  dsimp only [functor.right_op_map, quiver.hom.op_unop, quiver.hom.unop_op],
  rw massive_aux₁_assoc, congr' 1,
  ext1 x, simp only [comp_apply],
  dsimp only [ExtQprime_iso_aux_system_obj_aux', LCC_iso_Cond_of_top_ab,
    LCC_iso_Cond_of_top_ab_add_equiv, LCC_iso_Cond_of_top_ab_equiv, CLC, LC, functor.comp_map,
    Condensed.of_top_ab],
  simp only [add_equiv.to_fun_eq_coe, normed_group_hom.completion_coe_to_fun,
    add_equiv.to_AddCommGroup_iso_hom, add_equiv.coe_to_add_monoid_hom, add_equiv.trans_apply,
    add_equiv.ulift_apply, equiv.to_fun_as_coe, equiv.ulift_apply_2,
    Ab.ulift_map_apply_down, add_equiv.coe_mk, nat_iso.of_components.inv_app,
    add_equiv.to_AddCommGroup_iso, add_equiv.mk_symm,
    SemiNormedGroup.forget₂_Ab_map, normed_group_hom.coe_to_add_monoid_hom],
  let F := SemiNormedGroup.Completion.{u+1}.map ((SemiNormedGroup.LocallyConstant.{u+1 u}.obj
    (SemiNormedGroup.ulift.{u+1 u}.obj V)).map f.op),
  let g := _,
  let Z := _,
  change F ((uniform_space.completion.map g) Z) = _,
  change (F ∘ uniform_space.completion.map g) Z = _,
  erw [uniform_space.completion.map_comp],
  rotate,
  { apply normed_group_hom.uniform_continuous, },
  { apply normed_group_hom.uniform_continuous, },
  conv_lhs
  { dsimp only [function.comp, normed_group_hom.coe_to_add_monoid_hom, g,
      SemiNormedGroup.LocallyConstant_obj_map], },
  simp only [locally_constant.comap_hom_map_hom],
  letI : uniform_space.{u} (locally_constant.{u u} ↥(unop.{u+2} (op.{u+2} X)) ↥V) := _,
  erw [← uniform_space.completion.map_comp],
  rotate,
  { apply normed_group_hom.uniform_continuous, },
  { apply normed_group_hom.uniform_continuous, },
  dsimp only [function.comp, Z, quiver.hom.unop_op],
  congr' 1, clear Z g F,
  sorry
end

lemma massive (X Y : FreeAb Profinite.{u}) (f : X ⟶ Y) :
  (((preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab.{u} V.to_Cond Y.as).hom ≫
    (Condensed_Ab_to_presheaf.{u}.map (Condensed_LCC_iso_of_top_ab.{u} V).inv).app (op.{u+2} Y.as) ≫
    (ExtQprime_iso_aux_system_obj_aux'.{u} V Y.as).hom) ≫
    (𝟙 _)) ≫
    (forget₂.{u+2 u+2 u+1 u+1 u+1} SemiNormedGroup.{u+1} Ab.{u+1}).map
      (((CLC.{u+1 u} (SemiNormedGroup.ulift.{u+1 u}.obj V)).right_op.map_FreeAb ⋙
        FreeAb.eval.{u+1 u+2} SemiNormedGroup.{u+1}ᵒᵖ).map f).unop =
  (preadditive_yoneda.{u+1 u+2}.obj V.to_Cond).map
    ((freeCond.{u}.map_FreeAb ⋙ FreeAb.eval.{u+1 u+2} (Condensed.{u u+1 u+2} Ab.{u+1})).map f).op ≫
    ((preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab.{u} V.to_Cond X.as).hom ≫
    (Condensed_Ab_to_presheaf.{u}.map (Condensed_LCC_iso_of_top_ab.{u} V).inv).app (op.{u+2} X.as) ≫
    (ExtQprime_iso_aux_system_obj_aux'.{u} V X.as).hom) ≫  𝟙 _ :=
begin
  simp only [Condensed_Ab_to_presheaf_map, category.assoc, category.comp_id, functor.comp_map],
  dsimp only [Condensed_LCC_iso_of_top_ab, Sheaf.iso.mk_inv_val,
    iso_whisker_right_inv, whisker_right_app],
  apply free_abelian_group.induction_on f; clear f,
  { simp only [functor.map_zero, unop_zero, comp_zero, op_zero, zero_comp], },
  { apply massive_aux },
  { intros f hf,
    simp only [functor.map_neg, unop_neg, op_neg, comp_neg, neg_comp, hf], },
  { intros f g hf hg,
    simp only [functor.map_add, unop_add, op_add, comp_add, add_comp, hf, hg], },
end

lemma hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_c (c₁ c₂) (h : c₁ ⟶ c₂) :
  (hom_complex_QprimeFP_nat_iso_aux_system r' BD κ M V c₂).hom ≫
  (category_theory.functor.map _ h.op) =
  (category_theory.functor.map _
  begin
    refine homological_complex.op_functor.map (quiver.hom.op _),
    refine category_theory.functor.map _ h,
  end) ≫ (hom_complex_QprimeFP_nat_iso_aux_system r' BD κ M V c₁).hom :=
begin
  ext n : 2,
  have aux : ∀ (n : ℕ), (monotone.{0 0} (function.swap.{1 1 1} κ n)),
  { intro n, exact fact.out _ },
  haveI : fact (κ c₁ n ≤ κ c₂ n) := ⟨aux n h.le⟩,
  have := massive V
    (breen_deligne.FPsystem.X.{u} r' BD ⟨M⟩ κ c₁ n)
    (breen_deligne.FPsystem.X.{u} r' BD ⟨M⟩ κ c₂ n)
    ((breen_deligne.FP2.res.{u} r' _ _ _).app ⟨M⟩),
  exact this
end

lemma hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_κ (c : (ℝ≥0))
  [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ κ c n)] :
  (hom_complex_QprimeFP_nat_iso_aux_system r' BD κ M V c).hom ≫
  (whisker_right (aux_system.res _ _ _ _ _ _) _).app _ =
  begin
    refine category_theory.functor.map _ _,
    refine homological_complex.op_functor.map (quiver.hom.op _),
    refine (QprimeFP_nat.ι BD κ₂ κ M).app _,
  end ≫ (hom_complex_QprimeFP_nat_iso_aux_system r' BD κ₂ M V c).hom :=
begin
  ext n : 2,
  have := massive V
    (breen_deligne.FPsystem.X.{u} r' BD ⟨M⟩ κ₂ c n)
    (breen_deligne.FPsystem.X.{u} r' BD ⟨M⟩ κ c n)
    ((breen_deligne.FP2.res.{u} r' _ _ _).app ⟨M⟩),
  exact this
end

lemma hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_Tinv (c : ℝ≥0)
  [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ r' * κ c n)] :
  (hom_complex_QprimeFP_nat_iso_aux_system r' BD κ M V c).hom ≫
  (whisker_right
    (aux_system.Tinv _ _ _ _ _ _) _).app _ =
  begin
    refine category_theory.functor.map _ _,
    refine homological_complex.op_functor.map (quiver.hom.op _),
    refine (QprimeFP_nat.Tinv BD κ₂ κ M).app _,
  end
  ≫ (hom_complex_QprimeFP_nat_iso_aux_system r' BD κ₂ M V c).hom :=
begin
  ext n : 2,
  have := massive V
    (breen_deligne.FPsystem.X.{u} r' BD ⟨M⟩ κ₂ c n)
    (breen_deligne.FPsystem.X.{u} r' BD ⟨M⟩ κ c n)
    (((breen_deligne.FPsystem.Tinv.{u} r' BD ⟨M⟩ κ₂ κ).app c).f n),
  exact this,
end

def to_Cond_T_inv [normed_with_aut r V] : V.to_Cond ⟶ V.to_Cond :=
(Condensed.of_top_ab_map.{u} (normed_group_hom.to_add_monoid_hom.{u u} normed_with_aut.T.{u}.inv)
  (normed_group_hom.continuous _))

lemma hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_T_inv_aux (c : ℝ≥0)
  [normed_with_aut r V] (n : ℕ) (t) :
((forget₂.{u+2 u+2 u+1 u+1 u+1} SemiNormedGroup.{u+1} Ab.{u+1}).map
       (((aux_system.T_inv.{u u+1} r r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1 u}.obj V) κ).app
           (op.{1} c)).f n))
    ((((ExtQprime_iso_aux_system_obj_aux.{u} V).hom.app
           (((breen_deligne.FPsystem.{u} r' BD ⟨M⟩ κ).obj c).X n)).unop) t) =
  (((ExtQprime_iso_aux_system_obj_aux.{u} V).hom.app
        (((breen_deligne.FPsystem.{u} r' BD ⟨M⟩ κ).obj c).X n)).unop)
        (t ≫ to_Cond_T_inv.{u} r V) :=
begin
  /-
  Note: This should reduce to some calcuation with the sheafification adjunction,
  as well as something about completion/ulift compatibiity.
  If we can reduce this to such statements, we will be in pretty good shape.
  -/
  /- This code block is pretty slow.
  dsimp [ExtQprime_iso_aux_system_obj_aux, ExtQprime_iso_aux_system_obj_aux'],
  simp only [comp_apply],
  dsimp [forget₂, has_forget₂.forget₂, aux_system.T_inv,
    Condensed_LCC_iso_of_top_ab, LCC_iso_Cond_of_top_ab],
  rw nat_iso.of_components.inv_app,
  dsimp only [unop_op],
  -/
  sorry
end


lemma hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_T_inv (c : ℝ≥0)
  [normed_with_aut r V] :
(hom_complex_QprimeFP_nat_iso_aux_system.{u} r' BD κ M V c).hom ≫
  ((forget₂.{u+2 u+2 u+1 u+1 u+1} SemiNormedGroup.{u+1} Ab.{u+1}).map_homological_complex
       (complex_shape.up.{0} ℕ)).map (nat_trans.app
        ((aux_system.T_inv.{u u+1} r r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1 u}.obj V) κ)) _) =
  begin
    let e := preadditive_yoneda.map (to_Cond_T_inv r V),
    let e' := nat_trans.map_homological_complex e (complex_shape.down ℕ).symm,
    let Q := ((QprimeFP_nat r' BD κ M).obj c).op,
    exact e'.app Q,
  end ≫
  (hom_complex_QprimeFP_nat_iso_aux_system.{u} r' BD κ M V (c)).hom :=
begin
  ext n : 2, ext1 t,
  dsimp [hom_complex_QprimeFP_nat_iso_aux_system],
  simp only [comp_apply],
  dsimp [nat_iso.map_homological_complex, forget₂_unop],
  erw id_apply, erw id_apply,
  erw [functor.map_homological_complex_map_f],
  apply hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_T_inv_aux,
end

namespace ExtQprime_iso_aux_system_obj_naturality_setup

/-
lemma aux₁ (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) :
homological_complex.unop_functor.{u+2 u+1 0}.map
    (((preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
         forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
           AddCommGroup.{u+1}).right_op.map_homological_complex
        (complex_shape.up.{0} ℤ)).map
       ((homological_complex.embed.{0 0 u+2 u+1} complex_shape.embedding.nat_down_int_up).map
          ((QprimeFP_nat.{u} r' BD κ M).map h))).op ≫
  homological_complex.unop_functor.{u+2 u+1 0}.map
      ((map_homological_complex_embed.{u+2 u+2 u+1 u+1}
          (preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
             forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
               AddCommGroup.{u+1}).right_op).inv.app
         ((QprimeFP_nat.{u} r' BD κ M).obj c₁)).op ≫
    embed_unop.{u+2 u+1}.hom.app
      (op.{u+3}
         (((preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
              forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
                Ab.{u+1}).right_op.map_homological_complex
             (complex_shape.down.{0} ℕ)).obj
            ((QprimeFP_nat.{u} r' BD κ M).obj c₁))) =
  begin
    dsimp,
    let e := (QprimeFP_nat r' BD κ M).map h,
    let e₁ := ((preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
      forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
      Ab.{u+1}).right_op.map_homological_complex
      (complex_shape.down.{0} ℕ)).map e,
    let e₂ := homological_complex.unop_functor.map e₁.op,
    refine _ ≫
      (homological_complex.embed.{0 0 u+2 u+1} complex_shape.embedding.nat_up_int_down).map
      e₂,
    refine homological_complex.unop_functor.{u+2 u+1 0}.map
    ((map_homological_complex_embed.{u+2 u+2 u+1 u+1}
        (preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
           forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
             AddCommGroup.{u+1}).right_op).inv.app
       ((QprimeFP_nat.{u} r' BD κ M).obj c₂)).op ≫
    embed_unop.{u+2 u+1}.hom.app
    (op.{u+3}
       (((preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
            forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
              Ab.{u+1}).right_op.map_homological_complex
           (complex_shape.down.{0} ℕ)).obj
          ((QprimeFP_nat.{u} r' BD κ M).obj c₂)))
  end := admit

def F : ℝ≥0 ⥤
  (homological_complex.{u+1 u+2 0} AddCommGroup.{u+1} (complex_shape.down.{0} ℕ).symm)ᵒᵖ :=
QprimeFP_nat.{u} r' BD κ M ⋙
  (preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
     forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
       AddCommGroup.{u+1}).right_op.map_homological_complex
    (complex_shape.down.{0} ℕ) ⋙ homological_complex.unop_functor.right_op

@[reassoc]
lemma naturality_helper {c₁ c₂ : ℝ≥0} (h : c₁ ⟶ c₂) (n : ℕ) (w1 w2) :
  (homological_complex.homology_embed_nat_iso.{0 0 u+2 u+1} Ab.{u+1} complex_shape.embedding.nat_up_int_down
   nat_up_int_down_c_iff n (-↑n) w1).hom.app
    (((preadditive_yoneda.{u+1 u+2}.obj
    V.to_Cond).right_op.map_homological_complex (complex_shape.down.{0} ℕ)).obj
     ((QprimeFP_nat.{u} r' BD κ M).obj c₂)).unop ≫
     (homology_functor _ _ _).map
     (homological_complex.map_unop _ _ $
     category_theory.functor.map _ $ category_theory.functor.map _ h) =
  category_theory.functor.map _
  (homological_complex.map_unop _ _ $
    category_theory.functor.map _ $ category_theory.functor.map _ h) ≫
    (homological_complex.homology_embed_nat_iso.{0 0 u+2 u+1} Ab.{u+1} complex_shape.embedding.nat_up_int_down
  nat_up_int_down_c_iff n (-↑n) w2).hom.app
    (((preadditive_yoneda.{u+1 u+2}.obj
    V.to_Cond).right_op.map_homological_complex (complex_shape.down.{0} ℕ)).obj
    ((QprimeFP_nat.{u} r' BD κ M).obj c₁)).unop :=
admit
-/

lemma aux₁ (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (n : ℕ) :
  (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℕ) n).map
  (hom_complex_QprimeFP_nat_iso_aux_system.{u} r' BD κ M V c₂).hom ≫
  (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℕ) n).map
  ((aux_system.{u u+1} r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1 u}.obj V) κ).to_Ab.map h.op) =
  (homology_functor _ _ _).map
  (category_theory.functor.map _
      (homological_complex.op_functor.map ((QprimeFP_nat r' BD κ M).map h).op)) ≫
  (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℕ) n).map
  (hom_complex_QprimeFP_nat_iso_aux_system.{u} r' BD κ M V c₁).hom :=
begin
  rw [← functor.map_comp, ← functor.map_comp],
  congr' 1,
  erw ← hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_c,
end

lemma aux₂ (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (n : ℕ) :
  (homological_complex.homology_embed_nat_iso.{0 0 u+2 u+1} Ab.{u+1}
    complex_shape.embedding.nat_up_int_down nat_up_int_down_c_iff n (-↑n) (by { cases n; refl})).hom.app
    (hom_complex_nat.{u} ((QprimeFP_nat.{u} r' BD κ M).obj c₂) V.to_Cond) ≫
    (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℕ) n).map
    (((preadditive_yoneda.{u+1 u+2}.obj V.to_Cond).map_homological_complex
    (complex_shape.down.{0} ℕ).symm).map (homological_complex.op_functor.{u+2 u+1 0}.map
    ((QprimeFP_nat.{u} r' BD κ M).map h).op)) =
  (homological_complex.embed.{0 0 u+2 u+1} complex_shape.embedding.nat_up_int_down ⋙
  homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.down.{0} ℤ) (-↑n)).map
  (category_theory.functor.map _
      (homological_complex.op_functor.map ((QprimeFP_nat r' BD κ M).map h).op)) ≫
  (homological_complex.homology_embed_nat_iso.{0 0 u+2 u+1} Ab.{u+1}
  complex_shape.embedding.nat_up_int_down nat_up_int_down_c_iff n (-↑n) (by { cases n; refl})).hom.app
  (hom_complex_nat.{u} ((QprimeFP_nat.{u} r' BD κ M).obj c₁) V.to_Cond) :=
begin
  erw nat_trans.naturality,
end


lemma aux₃ (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (n : ℕ) :
  (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℤ).symm (-↑n)).map
  (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ M).obj c₂) V.to_Cond).hom ≫
  (homological_complex.embed.{0 0 u+2 u+1} complex_shape.embedding.nat_up_int_down ⋙
  homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.down.{0} ℤ) (-↑n)).map
  (((preadditive_yoneda.{u+1 u+2}.obj V.to_Cond).map_homological_complex
  (complex_shape.down.{0} ℕ).symm).map (homological_complex.op_functor.{u+2 u+1 0}.map
  ((QprimeFP_nat.{u} r' BD κ M).map h).op))
  =
  ((homology_functor.{u+1 u+2 0} AddCommGroup.{u+1}
  (complex_shape.up.{0} ℤ).symm (-↑n)).op.map
  (homological_complex.unop_functor.{u+2 u+1 0}.right_op.map
  (((preadditive_yoneda.{u+1 u+2}.obj V.to_Cond).right_op.map_homological_complex
  (complex_shape.up.{0} ℤ)).map ((QprimeFP_int.{u} r' BD κ M).map h)))).unop ≫
  (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℤ).symm (-↑n)).map
  (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ M).obj c₁) V.to_Cond).hom
  :=
begin
  dsimp only [functor.op_map, functor.comp_map],
  erw [← functor.map_comp],
  erw [← functor.map_comp],
  congr' 1,
  ext ((_ | k) | k ) : 2,
  { refine (category.id_comp _).trans (category.comp_id _).symm },
  { apply is_zero.eq_of_tgt,
    exact is_zero_zero _ },
  { refine (category.id_comp _).trans (category.comp_id _).symm },
end
/-
lemma naturality_helper {c₂ : ℝ≥0} (n : ℕ) :
  (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℤ).symm (-↑n)).map
  (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ M).obj c₂) V.to_Cond).hom ≫
  (homological_complex.homology_embed_nat_iso.{0 0 u+2 u+1} Ab.{u+1}
  complex_shape.embedding.nat_up_int_down nat_up_int_down_c_iff n (-↑n) (by { cases n; refl})).hom.app
  (hom_complex_nat.{u} ((QprimeFP_nat.{u} r' BD κ M).obj c₂) V.to_Cond) =
  _
-/

end ExtQprime_iso_aux_system_obj_naturality_setup

lemma QprimeFP_acyclic (c) (k i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (op (((QprimeFP_int.{u} r' BD κ M).obj c).X k))).obj V.to_Cond) :=
begin
  rcases k with ((_|k)|k),
  { apply free_acyclic, exact hi },
  { rw [← functor.flip_obj_obj], refine functor.map_is_zero _ _, refine (is_zero_zero _).op, },
  { apply free_acyclic, exact hi },
end

lemma ExtQprime_iso_aux_system_obj_natrality (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (n : ℕ) :
  (ExtQprime_iso_aux_system_obj r' BD κ M V c₂ n).hom ≫
  (homology_functor _ _ _).map
  ((system_of_complexes.to_Ab _).map h.op)  =
  ((Ext n).map ((QprimeFP r' BD κ _).map h).op).app _ ≫
  (ExtQprime_iso_aux_system_obj r' BD κ M V c₁ n).hom :=
begin
  dsimp only [ExtQprime_iso_aux_system_obj,
    iso.trans_hom, id, functor.map_iso_hom],
  haveI : ((homotopy_category.quotient.{u+1 u+2 0}
    (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ)).obj
     ((QprimeFP_int.{u} r' BD κ M).obj c₁)).is_bounded_above :=
    chain_complex.is_bounded_above _,
  haveI : ((homotopy_category.quotient.{u+1 u+2 0}
    (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ)).obj
     ((QprimeFP_int.{u} r' BD κ M).obj c₂)).is_bounded_above :=
    chain_complex.is_bounded_above _,
  have := Ext_compute_with_acyclic_naturality
    ((QprimeFP_int.{u} r' BD κ M).obj c₁)
    ((QprimeFP_int.{u} r' BD κ M).obj c₂)
    V.to_Cond _ _
    ((QprimeFP_int.{u} r' BD κ M).map h) n,
  rotate,
  { intros k i hi, apply QprimeFP_acyclic, exact hi },
  { intros k i hi, apply QprimeFP_acyclic, exact hi },
  dsimp only [functor.comp_map] at this,
  erw reassoc_of this, clear this,
  simp only [category.assoc, nat_iso.app_hom],
  congr' 1,
  rw ExtQprime_iso_aux_system_obj_naturality_setup.aux₁ r' BD κ M V c₁ c₂ h n,
  simp only [← category.assoc], congr' 1,
  simp only [category.assoc],
  rw ExtQprime_iso_aux_system_obj_naturality_setup.aux₂ r' BD κ M V c₁ c₂ h n,
  simp only [← category.assoc], congr' 1,

  exact ExtQprime_iso_aux_system_obj_naturality_setup.aux₃ r' BD κ M V c₁ c₂ h n,

  --- OLD PROOF FROM HERE
  --have := ExtQprime_iso_aux_system_obj_naturality_setup.naturality_helper r' BD κ
  --  M V h n _ _,
  --simp only [category.assoc, functor.map_comp],
  --slice_rhs 3 4
  --{ erw ← this },

  /-
  dsimp only [QprimeFP_int],
  congr' 1,
  dsimp only [nat_iso.app_hom],
  simp only [functor.map_comp, functor.comp_map, nat_trans.naturality,
    nat_trans.naturality_assoc],
  dsimp only [functor.op_map, quiver.hom.unop_op, functor.right_op_map],
  simp only [← functor.map_comp, ← functor.map_comp_assoc, category.assoc],
  dsimp [-homology_functor_map],
  rw ExtQprime_iso_aux_system_obj_naturality_setup.aux₁,
  dsimp [-homology_functor_map],
  simp only [functor.map_comp, functor.map_comp_assoc,
    category.assoc, nat_trans.naturality_assoc],
  congr' 2,
  dsimp [-homology_functor_map],
  dsimp only [← functor.comp_map, ← functor.comp_obj],
  --erw nat_trans.naturality_assoc,
  --refine congr_arg2 _ _ (congr_arg2 _ rfl _),

  --congr' 1,
  --refl,
  admit

  -/
end

def ExtQprime_iso_aux_system (n : ℕ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ≅
  aux_system r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ ⋙
    (forget₂ _ Ab).map_homological_complex _ ⋙ homology_functor _ _ n :=
nat_iso.of_components (λ c, ExtQprime_iso_aux_system_obj r' BD κ M V (unop c) n)
begin
  intros c₁ c₂ h,
  dsimp [-homology_functor_map],
  rw ← ExtQprime_iso_aux_system_obj_natrality,
  refl,
end

/-- The `Tinv` map induced by `M` -/
def ExtQprime.Tinv
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (n : ℤ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ⟶
  (QprimeFP r' BD κ₂ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) :=
whisker_right (nat_trans.op $ QprimeFP.Tinv BD _ _ M) _

/-- The `T_inv` map induced by `V` -/
def ExtQprime.T_inv [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (n : ℤ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ⟶
  (QprimeFP r' BD κ₂ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) :=
whisker_right (nat_trans.op $ QprimeFP.ι BD _ _ M) _ ≫ whisker_left _ ((Ext n).flip.map $ (single _ _).map $
  (Condensed.of_top_ab_map (normed_with_aut.T.inv).to_add_monoid_hom
  (normed_group_hom.continuous _)))

def ExtQprime.Tinv2 [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (n : ℤ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ⟶
  (QprimeFP r' BD κ₂ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) :=
ExtQprime.Tinv r' BD κ κ₂ M V n - ExtQprime.T_inv r r' BD κ κ₂ M V n

namespace ExtQprime_iso_aux_system_comm_Tinv_setup

variables (c : (ℝ≥0)ᵒᵖ) (n : ℕ)
  [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ r' * κ c n)]

lemma aux₁  :
(homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℕ) n).map
    (hom_complex_QprimeFP_nat_iso_aux_system.{u} r' BD κ M V (unop.{1} c)).hom ≫
  ((forget₂.{u+2 u+2 u+1 u+1 u+1} SemiNormedGroup.{u+1} Ab.{u+1}).map_homological_complex
       (complex_shape.up.{0} ℕ) ⋙
     homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℕ) n).map
    ((aux_system.Tinv.{u u+1} r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1 u}.obj V) κ₂ κ).app c) =
  (homology_functor _ _ _).map
  (category_theory.functor.map _
      (homological_complex.op_functor.map (quiver.hom.op $
      (QprimeFP_nat.Tinv  BD κ₂ κ M).app _))) ≫
  (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℕ) n).map
  (hom_complex_QprimeFP_nat_iso_aux_system.{u} r' BD κ₂ M V (unop.{1} c)).hom :=
begin
  simp only [← functor.map_comp, functor.comp_map], congr' 1,
  apply hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_Tinv,
end

lemma aux₂ :
(homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℤ).symm (-↑n)).map
      (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ M).obj (unop.{1} c)) V.to_Cond).hom ≫
    (homological_complex.embed.{0 0 u+2 u+1} complex_shape.embedding.nat_up_int_down ⋙
       homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.down.{0} ℤ) (-↑n)).map
      (((preadditive_yoneda.{u+1 u+2}.obj V.to_Cond).map_homological_complex (complex_shape.down.{0} ℕ).symm).map
         (homological_complex.op_functor.{u+2 u+1 0}.map ((QprimeFP_nat.Tinv.{u} BD κ₂ κ M).app (unop.{1} c)).op)) =
  (((preadditive_yoneda.{u+1 u+2}.obj V.to_Cond).right_op.map_homological_complex (complex_shape.up.{0} ℤ) ⋙
        homological_complex.unop_functor.{u+2 u+1 0}.right_op ⋙
          (homology_functor.{u+1 u+2 0} AddCommGroup.{u+1} (complex_shape.up.{0} ℤ).symm (-↑n)).op).map
       ((QprimeFP_int.Tinv.{u} BD κ₂ κ M).app (unop.{1} c))).unop ≫
    (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℤ).symm (-↑n)).map
      (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ₂ M).obj (unop.{1} c)) V.to_Cond).hom :=
begin
  dsimp only [functor.op_map, functor.comp_map],
  erw [← functor.map_comp],
  erw [← functor.map_comp],
  congr' 1,
  ext ((_ | k) | k ) : 2,
  { refine (category.id_comp _).trans (category.comp_id _).symm },
  { apply is_zero.eq_of_tgt,
    exact is_zero_zero _ },
  { refine (category.id_comp _).trans (category.comp_id _).symm },
end

end ExtQprime_iso_aux_system_comm_Tinv_setup

lemma ExtQprime_iso_aux_system_comm_Tinv
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
  (ExtQprime_iso_aux_system r' BD κ M V n).hom ≫
  whisker_right (aux_system.Tinv.{u} r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ₂ κ)
    ((forget₂ _ _).map_homological_complex _ ⋙ homology_functor Ab.{u+1} (complex_shape.up ℕ) n) =
  ExtQprime.Tinv r' BD κ κ₂ M V n ≫
  (ExtQprime_iso_aux_system r' BD κ₂ M V n).hom :=
begin
  ext c : 2,
  dsimp only [ExtQprime_iso_aux_system_obj,
    ExtQprime_iso_aux_system,
    iso.trans_hom, id, functor.map_iso_hom, nat_iso.of_components.hom_app,
    nat_trans.comp_app],
  haveI : ((homotopy_category.quotient.{u+1 u+2 0} (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ)).obj
     ((QprimeFP_int.{u} r' BD κ M).obj (unop.{1} c))).is_bounded_above :=
     chain_complex.is_bounded_above _,
  haveI : ((homotopy_category.quotient.{u+1 u+2 0} (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ)).obj
     ((QprimeFP_int.{u} r' BD κ₂ M).obj (unop.{1} c))).is_bounded_above :=
     chain_complex.is_bounded_above _,
  have := Ext_compute_with_acyclic_naturality
    ((QprimeFP_int.{u} r' BD κ₂ M).obj c.unop)
    ((QprimeFP_int.{u} r' BD κ M).obj c.unop)
    V.to_Cond _ _
    ((QprimeFP_int.Tinv BD κ₂ κ M).app _) n,
  rotate,
  { intros k i hi, apply QprimeFP_acyclic, exact hi },
  { intros k i hi, apply QprimeFP_acyclic, exact hi },
  erw reassoc_of this, clear this, simp only [category.assoc], congr' 1,
  dsimp only [whisker_right_app],
  rw ExtQprime_iso_aux_system_comm_Tinv_setup.aux₁ r' BD κ κ₂ M V c n,
  simp only [← category.assoc], congr' 1, simp only [category.assoc],
  erw ← nat_trans.naturality,
  simp only [← category.assoc], congr' 1,
  exact ExtQprime_iso_aux_system_comm_Tinv_setup.aux₂ r' BD κ κ₂ M V c n,
end


-- lemma ExtQprime_iso_aux_system_comm_T_inv [normed_with_aut r V] (n : ℕ) (c : ℝ≥0ᵒᵖ) :
--   (ExtQprime_iso_aux_system_obj.{u} r' BD κ₂ M V (unop.{1} c) n).hom ≫
--     ((forget₂.{u+2 u+2 u+1 u+1 u+1} SemiNormedGroup.{u+1} Ab.{u+1}).map_homological_complex (complex_shape.up.{0} ℕ) ⋙
--    homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℕ) n).map
--   ((aux_system.res.{u u+1} r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1 u}.obj V) κ₂ κ).app c) =
--   ((Ext.{u+1 u+2} ↑n).flip.map
--       ((single.{u+1 u+2} (Condensed.{u u+1 u+2} Ab.{u+1}) 0).map
--           (Condensed.of_top_ab_map.{u} (normed_group_hom.to_add_monoid_hom.{u u} normed_with_aut.T.{u}.inv) _))).app
--       ((QprimeFP.{u} r' BD κ₂ M).op.obj c) ≫
--     (ExtQprime_iso_aux_system_obj.{u} r' BD κ₂ M V (unop.{1} c) n).hom :=
-- by admit

def homological_complex.map_unop {A M : Type*} [category A] [abelian A]
  {c : complex_shape M} (C₁ C₂ : homological_complex Aᵒᵖ c) (f : C₁ ⟶ C₂) :
  C₂.unop ⟶ C₁.unop :=
homological_complex.unop_functor.map f.op

namespace ExtQprime_iso_aux_system_comm_setup

include r
variables [normed_with_aut r V] [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ κ c n)]

def hom_complex_map_T_inv (c : (ℝ≥0)ᵒᵖ) :
  hom_complex_nat.{u} ((QprimeFP_nat.{u} r' BD κ M).obj (unop.{1} c)) V.to_Cond ⟶
  hom_complex_nat.{u} ((QprimeFP_nat.{u} r' BD κ₂ M).obj (unop.{1} c)) V.to_Cond :=
  begin
    refine nat_trans.app _ _,
    refine nat_trans.map_homological_complex _ _,
    refine preadditive_yoneda.map _,
    refine Condensed.of_top_ab_map.{u} (normed_group_hom.to_add_monoid_hom.{u u}
      normed_with_aut.T.{u}.inv) (normed_group_hom.continuous _)
  end ≫
  (category_theory.functor.map _
      (homological_complex.op_functor.map (quiver.hom.op $
      (QprimeFP_nat.ι BD κ₂ κ M).app _)))

omit r

lemma embed_hom_complex_nat_iso₀ (c : (ℝ≥0)ᵒᵖ) : (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ₂ M).obj (unop.{1} c)) V.to_Cond).hom.f (int.of_nat 0) = 𝟙 _ := rfl

lemma embed_hom_complex_nat_iso_neg (n : ℕ) (c : (ℝ≥0)ᵒᵖ) : (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ₂ M).obj (unop.{1} c)) V.to_Cond).hom.f (-[1+ n]) = 𝟙 _ := rfl


lemma add_equiv.to_AddCommGroup_iso_apply (A B : AddCommGroup.{u})
  (e : A ≃+ B) (a : A) : e.to_AddCommGroup_iso.hom a = e a := rfl

lemma preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab_apply (M) (X) (t) :
  (preadditive_yoneda_obj_obj_CondensedSet_to_Condensed_Ab M X).hom t =
  yoneda'_equiv _ _ (Condensed_Ab_CondensedSet_adjunction.hom_equiv X.to_Condensed M t).val := rfl

include r

lemma aux₁ (c : (ℝ≥0)ᵒᵖ):
(hom_complex_QprimeFP_nat_iso_aux_system.{u} r' BD κ M V (unop.{1} c)).hom ≫
  ((forget₂.{u+2 u+2 u+1 u+1 u+1} SemiNormedGroup.{u+1} Ab.{u+1}).map_homological_complex
     (complex_shape.up.{0} ℕ)).map ((aux_system.T_inv.{u u+1} r r' BD
    ⟨M⟩ (SemiNormedGroup.ulift.{u+1 u}.obj V) κ).app c ≫
  (aux_system.res.{u u+1} r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1 u}.obj V) κ₂ κ).app c) =
  hom_complex_map_T_inv _ _ _ _ _ _ _ _ ≫
  (hom_complex_QprimeFP_nat_iso_aux_system.{u} r' BD κ₂ M V (unop.{1} c)).hom :=
begin
  --simp only [← category_theory.functor.map_comp, functor.comp_map], congr' 1,
  dsimp only [hom_complex_map_T_inv], simp only [category.assoc],
  rw ← hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_κ r' BD κ κ₂ M V c.unop,
  simp only [functor.map_comp, ← category.assoc], congr' 1,
  apply hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_T_inv

  /- -- IGNORE THIS
  ext k t : 3,
  dsimp [hom_complex_nat] at t,
  dsimp only [hom_complex_QprimeFP_nat_iso_aux_system, aux_system.T_inv,
    aux_system.res, hom_complex_nat, functor.map_iso, iso.trans_hom,
    homological_complex.unop_functor, homological_complex.comp_f,
    nat_iso.map_homological_complex, nat_iso.app_hom, iso.op_hom, quiver.hom.unop_op,
    nat_trans.map_homological_complex_app_f, ExtQprime_iso_aux_system_obj_aux,
    nat_iso.of_components.hom_app, id, iso.symm_hom, nat_iso.app_inv,
    whisker_right_app, nat_trans.op, functor.comp_map],
  simp only [category_theory.functor.map_comp],
  dsimp only [homological_complex.comp_f, functor.map_homological_complex, functor.op_obj,
    functor.unop, forget₂_unop, nat_iso.of_components.hom_app,
    homological_complex.hom.iso_of_components, iso.refl],
  simp only [category.assoc, category.id_comp],
  erw category.id_comp,
  dsimp only [functor.op, quiver.hom.unop_op],
  erw category.comp_id,
  repeat { rw [comp_apply] },
  -/ -- UUUUGGGHHH

end

lemma aux₂ (c : (ℝ≥0)ᵒᵖ) :
((((preadditive_yoneda.{u+1 u+2}.obj (Condensed.of_top_ab.{u} ↥V)).right_op.map_homological_complex
         (complex_shape.up.{0} ℤ)).obj
        ((QprimeFP_int.{u} r' BD κ M).obj (unop.{1} c))).map_unop
       (((preadditive_yoneda.{u+1 u+2}.obj (Condensed.of_top_ab.{u} ↥V)).right_op.map_homological_complex
           (complex_shape.up.{0} ℤ)).obj
          ((QprimeFP_int.{u} r' BD κ M).obj (unop.{1} c)))
       ((nat_trans.map_homological_complex.{u+1 u+2 0 u+2 u+1}
           (nat_trans.right_op.{u+1 u+1 u+2 u+2} (preadditive_yoneda.{u+1 u+2}.map
           (Condensed.of_top_ab_map.{u} (normed_group_hom.to_add_monoid_hom.{u u}
        normed_with_aut.T.{u}.inv) (normed_group_hom.continuous _))))
           (complex_shape.up.{0} ℤ)).app
          ((QprimeFP_int.{u} r' BD κ M).obj (unop.{1} c))) ≫
     (homological_complex.unop_functor.{u+2 u+1 0}.right_op.map
        (((preadditive_yoneda.{u+1 u+2}.obj V.to_Cond).right_op.map_homological_complex (complex_shape.up.{0} ℤ)).map
           ((QprimeFP_int.ι.{u} BD κ₂ κ M).app (unop.{1} c)))).unop) ≫
  (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ₂ M).obj (unop.{1} c)) V.to_Cond).hom =
  (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ M).obj (unop.{1} c)) V.to_Cond).hom ≫
  category_theory.functor.map _
  (hom_complex_map_T_inv _ _ _ _ _ _ _ _) :=
begin
  ext ((_ | k) | k ) : 2,
  { dsimp only [functor.comp],
    simp only [functor.right_op_map, quiver.hom.unop_op, category.assoc, homological_complex.comp_f,
  homological_complex.unop_functor_map_f, functor.map_homological_complex_map_f],
  rw embed_hom_complex_nat_iso₀,
  rw embed_hom_complex_nat_iso₀,
  ext, refl },
  { apply is_zero.eq_of_tgt,
    exact is_zero_zero _ },
  { dsimp only [functor.comp],
    simp only [functor.right_op_map, quiver.hom.unop_op, category.assoc, homological_complex.comp_f,
  homological_complex.unop_functor_map_f, functor.map_homological_complex_map_f],
  rw embed_hom_complex_nat_iso_neg,
  rw embed_hom_complex_nat_iso_neg,
  ext, refl },
end

end ExtQprime_iso_aux_system_comm_setup

section naturality_snd_var

variables {A : Type*} [category A] [abelian A] [enough_projectives A]
  (X : cochain_complex A ℤ)
  [((homotopy_category.quotient A (complex_shape.up.{0} ℤ)).obj X).is_bounded_above]
  {B₁ B₂ : A} (f : B₁ ⟶ B₂) -- (h₁) (h₂) (i)

@[reassoc]
lemma Ext_compute_with_acyclic_aux₁_naturality_snd_var (i)
  (e : (0 : ℤ) - i = -i) :
  (Ext_compute_with_acyclic_aux₁ X B₁ i).hom ≫
  begin
    refine nat_trans.app _ _,
    refine preadditive_yoneda.map _,
    refine category_theory.functor.map _ f,
  end =
  category_theory.functor.map _
  (category_theory.functor.map _ f) ≫
  (Ext_compute_with_acyclic_aux₁ X B₂ i).hom :=
begin
  ext t,
  simp only [comp_apply],
  dsimp [Ext_compute_with_acyclic_aux₁, Ext],
  simp only [category.assoc],
  generalize_proofs h1 h2,
  let φ₁ := λ j, (single _ j).obj B₁,
  let φ₂ := λ j, (single _ j).obj B₂,
  change t ≫ _ ≫ eq_to_hom (congr_arg φ₁ e) ≫ _ =
    _ ≫ _ ≫ _ ≫ eq_to_hom (congr_arg φ₂ e),
  induction e,
  dsimp, simp only [category.id_comp, category.comp_id],
  erw ← nat_trans.naturality,
  refl,
end

@[reassoc]
lemma Ext_compute_with_acyclic_aux₂_naturality_snd_var (i) :
  (Ext_compute_with_acyclic_aux₂ X B₁ i).hom ≫
  (homology_functor _ _ _).map
  begin
    refine nat_trans.app _ _,
    refine nat_trans.map_homological_complex _ _,
    exact preadditive_yoneda.map f,
  end =
  nat_trans.app
  (preadditive_yoneda.map $ category_theory.functor.map _ f) _ ≫
  (Ext_compute_with_acyclic_aux₂ X B₂ i).hom :=
begin
  dsimp only [Ext_compute_with_acyclic_aux₂, unop_op],
  have := hom_single_iso_naturality_snd_var_good (of' X).replace (-i) f,
  erw ← this,
end

include f
lemma Ext_compute_with_acyclic_aux₃_naturality_snd_var (i) :
  (homology_functor _ _ _).map
  begin
    refine homological_complex.map_unop _ _ _,
    refine nat_trans.app _ _,
    refine nat_trans.map_homological_complex _ _,
    refine nat_trans.right_op _,
    exact preadditive_yoneda.map f,
  end ≫ Ext_compute_with_acyclic_aux₃ X B₂ i =
  Ext_compute_with_acyclic_aux₃ X B₁ i ≫
  (homology_functor _ _ _).map
  begin
    refine nat_trans.app _ _,
    refine nat_trans.map_homological_complex _ _,
    exact preadditive_yoneda.map f,
  end :=
begin
  dsimp only [Ext_compute_with_acyclic_aux₃],
  erw ← (homology_functor.{u_2 u_2+1 0} AddCommGroup.{u_2}
    (complex_shape.up.{0} ℤ).symm (-i)).map_comp,
  erw ← (homology_functor.{u_2 u_2+1 0} AddCommGroup.{u_2}
    (complex_shape.up.{0} ℤ).symm (-i)).map_comp,
  congr' 1,
  ext t x,
  dsimp [Ext_compute_with_acyclic_HomB],
  simp only [comp_apply],
  dsimp [nat_trans.map_homological_complex, functor.right_op,
    homological_complex.map_unop],
  simp only [category.assoc],
end

lemma Ext_compute_with_acyclic_naturality_snd_var
  (h₁) (h₂) (i) :
  (Ext_compute_with_acyclic X B₁ h₁ i).hom ≫
  (homology_functor _ _ _).map
  (begin
    refine homological_complex.map_unop _ _ _,
    refine nat_trans.app _ _,
    refine nat_trans.map_homological_complex _ _,
    exact (preadditive_yoneda.map f).right_op,
  end) =
  category_theory.functor.map _
  (category_theory.functor.map _ f) ≫ (Ext_compute_with_acyclic X B₂ h₂ i).hom :=
begin
  dsimp [Ext_compute_with_acyclic, - homology_functor_map],
  simp only [category.assoc],
  rw ← Ext_compute_with_acyclic_aux₁_naturality_snd_var_assoc,
  rw ← Ext_compute_with_acyclic_aux₂_naturality_snd_var_assoc,
  simp only [category.assoc], congr' 2,
  rw [is_iso.eq_comp_inv, category.assoc, is_iso.inv_comp_eq],
  apply Ext_compute_with_acyclic_aux₃_naturality_snd_var,
  simp,
end

end naturality_snd_var

lemma ExtQprime_iso_aux_system_comm [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
  (ExtQprime_iso_aux_system r' BD κ M V n).hom ≫
  whisker_right (aux_system.Tinv2.{u} r r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ₂ κ)
    ((forget₂ _ _).map_homological_complex _ ⋙ homology_functor Ab.{u+1} (complex_shape.up ℕ) n) =
  ExtQprime.Tinv2 r r' BD κ κ₂ M V n ≫
  (ExtQprime_iso_aux_system r' BD κ₂ M V n).hom :=
begin
  ext c : 2, dsimp only [aux_system.Tinv2, ExtQprime.Tinv2, nat_trans.comp_app, whisker_right_app],
  simp only [sub_comp, nat_trans.app_sub, functor.map_sub, comp_sub],
  refine congr_arg2 _ _ _,
  { rw [← nat_trans.comp_app, ← ExtQprime_iso_aux_system_comm_Tinv], refl },

  dsimp only [ExtQprime_iso_aux_system_obj,
    ExtQprime_iso_aux_system,
    iso.trans_hom, id, functor.map_iso_hom, nat_iso.of_components.hom_app,
    nat_trans.comp_app],

  haveI : ((homotopy_category.quotient.{u+1 u+2 0} (Condensed.{u u+1 u+2} Ab.{u+1})
    (complex_shape.up.{0} ℤ)).obj
     ((QprimeFP_int.{u} r' BD κ M).obj (unop.{1} c))).is_bounded_above :=
     chain_complex.is_bounded_above _,
  haveI : ((homotopy_category.quotient.{u+1 u+2 0} (Condensed.{u u+1 u+2} Ab.{u+1})
    (complex_shape.up.{0} ℤ)).obj
     ((QprimeFP_int.{u} r' BD κ₂ M).obj (unop.{1} c))).is_bounded_above :=
     chain_complex.is_bounded_above _,
  have := Ext_compute_with_acyclic_naturality
    ((QprimeFP_int.{u} r' BD κ₂ M).obj c.unop)
    ((QprimeFP_int.{u} r' BD κ M).obj c.unop)
    V.to_Cond _ _
    ((QprimeFP_int.ι BD κ₂ κ M).app _) n,
  rotate,
  { intros k i hi, apply QprimeFP_acyclic, exact hi },
  { intros k i hi, apply QprimeFP_acyclic, exact hi },

  simp only [category.assoc], dsimp only [ExtQprime.T_inv, nat_trans.comp_app,
    whisker_right_app, whisker_left_app, functor.flip],
  let η := (Ext.{u+1 u+2} ↑n).map ((nat_trans.op.{0 u+1 0 u+2} (QprimeFP.ι.{u} BD κ₂ κ M)).app c),

  slice_rhs 1 2 { erw ← η.naturality },
  slice_rhs 2 3 { erw this },
  simp only [category.assoc], clear this η,

  let t : Condensed.of_top_ab V ⟶ _ :=
    Condensed.of_top_ab_map.{u} (normed_group_hom.to_add_monoid_hom.{u u}
      normed_with_aut.T.{u}.inv) (normed_group_hom.continuous _),
  have := Ext_compute_with_acyclic_naturality_snd_var
    ((QprimeFP_int r' BD κ M).obj c.unop) t _ _ n,
  rotate,
  { intros k i hi, apply QprimeFP_acyclic, exact hi },
  { intros k i hi, apply QprimeFP_acyclic, exact hi },
  erw ← reassoc_of this, clear this, congr' 1,
  simp only [functor.comp_map, category_theory.functor.map_comp,
    functor.op_map, quiver.hom.unop_op],
  slice_rhs 1 2 { rw ← category_theory.functor.map_comp },
  slice_lhs 4 5 { rw ← category_theory.functor.map_comp },
  simp only [category.assoc,
    ← category_theory.functor.map_comp, ← functor.map_comp_assoc],

  rw ExtQprime_iso_aux_system_comm_setup.aux₁ r r' BD κ κ₂ M V c,
  slice_lhs 2 4
  { simp only [category_theory.functor.map_comp] },

  simp only [← category.assoc], congr' 1,

  rw ExtQprime_iso_aux_system_comm_setup.aux₂ r r' BD κ κ₂ M V c,
  simp only [category_theory.functor.map_comp, category.assoc],
  congr' 1,

  rw [nat_iso.app_hom, ← nat_trans.naturality],
  congr' 1,

  -- have := Ext_compute_with_acyclic_naturality, <-- we need naturality in the other variable?!

  --simp only [category.assoc],
  --erw reassoc_of this,
   --clear this, simp only [category.assoc], congr' 1,

  /-
  rw [nat_trans.comp_app, functor.map_comp, ExtQprime.T_inv,
    nat_trans.comp_app, whisker_right_app, whisker_left_app, category.assoc],
  dsimp only [ExtQprime_iso_aux_system, nat_iso.of_components.hom_app, aux_system,
    aux_system.res, functor.comp_map],
  -/
end

lemma ExtQprime_iso_aux_system_comm' [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
  whisker_right (aux_system.Tinv2.{u} r r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ₂ κ)
    ((forget₂ _ _).map_homological_complex _ ⋙ homology_functor Ab.{u+1} (complex_shape.up ℕ) n) ≫
  (ExtQprime_iso_aux_system r' BD κ₂ M V n).inv =
  (ExtQprime_iso_aux_system r' BD κ M V n).inv ≫
  ExtQprime.Tinv2 r r' BD κ κ₂ M V n :=
begin
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp],
  apply ExtQprime_iso_aux_system_comm
end

end

section

def _root_.category_theory.functor.map_commsq
  {C D : Type*} [category C] [abelian C] [category D] [abelian D] (F : C ⥤ D) {X Y Z W : C}
  {f₁ : X ⟶ Y} {g₁ : X ⟶ Z} {g₂ : Y ⟶ W} {f₂ : Z ⟶ W} (sq : commsq f₁ g₁ g₂ f₂) :
  commsq (F.map f₁) (F.map g₁) (F.map g₂) (F.map f₂) :=
commsq.of_eq $ by rw [← F.map_comp, sq.w, F.map_comp]

end

section

variables {r'}
variables (BD : breen_deligne.package)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.data.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

open bounded_homotopy_category

-- move me
instance eval'_is_bounded_above :
  ((homotopy_category.quotient (Condensed Ab) (complex_shape.up ℤ)).obj
    ((BD.eval' freeCond').obj M.to_Condensed)).is_bounded_above :=
by { delta breen_deligne.package.eval', refine ⟨⟨1, _⟩⟩, apply chain_complex.bounded_by_one }

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

def Ext_Tinv2
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A B V : bounded_homotopy_category 𝓐}
  (Tinv : A ⟶ B) (ι : A ⟶ B) (T_inv : V ⟶ V) (i : ℤ) :
  ((Ext i).obj (op B)).obj V ⟶ ((Ext i).obj (op A)).obj V :=
(((Ext i).map Tinv.op).app V - (((Ext i).map ι.op).app V ≫ ((Ext i).obj _).map T_inv))

open category_theory.preadditive

def Ext_Tinv2_commsq
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A₁ B₁ A₂ B₂ V : bounded_homotopy_category 𝓐}
  (Tinv₁ : A₁ ⟶ B₁) (ι₁ : A₁ ⟶ B₁)
  (Tinv₂ : A₂ ⟶ B₂) (ι₂ : A₂ ⟶ B₂)
  (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (sqT : f ≫ Tinv₂ = Tinv₁ ≫ g) (sqι : f ≫ ι₂ = ι₁ ≫ g)
  (T_inv : V ⟶ V) (i : ℤ) :
  commsq
    (((Ext i).map g.op).app V)
    (Ext_Tinv2 Tinv₂ ι₂ T_inv i)
    (Ext_Tinv2 Tinv₁ ι₁ T_inv i)
    (((Ext i).map f.op).app V) :=
commsq.of_eq
begin
  delta Ext_Tinv2,
  simp only [comp_sub, sub_comp, ← nat_trans.comp_app, ← functor.map_comp, ← op_comp, sqT,
    ← nat_trans.naturality, ← nat_trans.naturality_assoc, category.assoc, sqι],
end

open category_theory.preadditive

lemma auux
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A₁ B₁ A₂ B₂ : cochain_complex 𝓐 ℤ}
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A₁).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj B₁).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A₂).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj B₂).is_bounded_above]
  {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂} {α : A₁ ⟶ A₂} {β : B₁ ⟶ B₂}
  (sq1 : commsq f₁ α β f₂) :
  of_hom f₁ ≫ of_hom β = of_hom α ≫ of_hom f₂ :=
begin
  have := sq1.w,
  apply_fun (λ f, (homotopy_category.quotient _ _).map f) at this,
  simp only [functor.map_comp] at this,
  exact this,
end

@[simp] lemma of_hom_id
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A : cochain_complex 𝓐 ℤ}
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A).is_bounded_above] :
  of_hom (𝟙 A) = 𝟙 _ :=
by { delta of_hom, rw [category_theory.functor.map_id], refl }

lemma Ext_iso_of_bicartesian_of_bicartesian
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A₁ B₁ C A₂ B₂ : cochain_complex 𝓐 ℤ}
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A₁).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj B₁).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj C).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A₂).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj B₂).is_bounded_above]
  {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C} (w₁ : ∀ n, short_exact (f₁.f n) (g₁.f n))
  {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C} (w₂ : ∀ n, short_exact (f₂.f n) (g₂.f n))
  (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (γ : C ⟶ C)
  (ιA : A₁ ⟶ A₂) (ιB : B₁ ⟶ B₂)
  (sq1 : commsq f₁ α β f₂) (sq2 : commsq g₁ β γ g₂)
  (sq1' : commsq f₁ ιA ιB f₂) (sq2' : commsq g₁ ιB (𝟙 _) g₂)
  (V : bounded_homotopy_category 𝓐) (T_inv : V ⟶ V)
  (i : ℤ)
  (H1 : (Ext_Tinv2_commsq (of_hom α) (of_hom ιA) (of_hom β) (of_hom ιB) (of_hom f₁) (of_hom f₂)
    (auux sq1) (auux sq1') T_inv i).bicartesian)
  (H2 : (Ext_Tinv2_commsq (of_hom α) (of_hom ιA) (of_hom β) (of_hom ιB) (of_hom f₁) (of_hom f₂)
    (auux sq1) (auux sq1') T_inv (i+1)).bicartesian) :
  is_iso (Ext_Tinv2 (of_hom γ) (𝟙 _) T_inv (i+1)) :=
begin
  have LES₁ := (((Ext_five_term_exact_seq' _ _ i V w₁).drop 2).pair.cons (Ext_five_term_exact_seq' _ _ (i+1) V w₁)),
  replace LES₁ := (((Ext_five_term_exact_seq' _ _ i V w₁).drop 1).pair.cons LES₁).extract 0 4,
  have LES₂ := (((Ext_five_term_exact_seq' _ _ i V w₂).drop 2).pair.cons (Ext_five_term_exact_seq' _ _ (i+1) V w₂)).extract 0 4,
  replace LES₂ := (((Ext_five_term_exact_seq' _ _ i V w₂).drop 1).pair.cons LES₂).extract 0 4,
  refine iso_of_bicartesian_of_bicartesian LES₂ LES₁ _ _ _ _ H1 H2,
  { apply commsq.of_eq, delta Ext_Tinv2, clear LES₁ LES₂,
    rw [sub_comp, comp_sub, ← functor.flip_obj_map, ← functor.flip_obj_map],
    rw ← Ext_δ_natural i V _ _ _ _ α β γ sq1.w sq2.w w₁ w₂,
    congr' 1,
    rw [← nat_trans.naturality, ← functor.flip_obj_map, category.assoc,
      Ext_δ_natural i V _ _ _ _ ιA ιB (𝟙 _) sq1'.w sq2'.w w₁ w₂],
    simp only [op_id, category_theory.functor.map_id, nat_trans.id_app,
      category.id_comp, of_hom_id, category.comp_id],
    erw [category.id_comp],
    symmetry,
    apply Ext_δ_natural', },
  { apply Ext_Tinv2_commsq,
    { exact auux sq2 },
    { exact auux sq2' }, },
end

end
