import free_pfpng.epi
import free_pfpng.mono

noncomputable theory

open_locale classical big_operators

open category_theory
open opposite
open category_theory.grothendieck_topology

universe u

lemma Condensed.is_zero_of_is_zero_obj (A : Condensed.{u} Ab.{u+1})
  (hA : ∀ S : Profinite.{u}, limits.is_zero (A.val.obj (opposite.op S))) :
  limits.is_zero A :=
{ unique_to := λ Y, nonempty.intro
  { default := 0,
    uniq := λ a, begin
      ext t : 3,
      apply (hA t.unop).eq_of_src,
    end },
  unique_from := λ Y, nonempty.intro
  { default := 0,
    uniq := λ a, begin
      ext t : 3,
      apply (hA t.unop).eq_of_tgt
    end } }

lemma Profinite.free_pfpng_eq_zero_of_empty (S : Profinite.{u}) [is_empty S]
  (a : S.free_pfpng) : a = 0 :=
begin
  let E : limits.cone ((S.fintype_diagram ⋙ free_pfpng_functor)) :=
    ProFiltPseuNormGrp₁.bounded_cone ⟨Ab.explicit_limit_cone _,
      Ab.explicit_limit_cone_is_limit _⟩,
  let hE : limits.is_limit E :=
    ProFiltPseuNormGrp₁.bounded_cone_is_limit _,
  let ee : S.free_pfpng ≅ E.X :=
    (limits.limit.is_limit _).cone_point_unique_up_to_iso hE,
  apply_fun ee.hom, swap,
  { intros x y h, apply_fun ee.inv at h, simpa using h },
  rw ee.hom.map_zero, ext T t,
  obtain ⟨s⟩ := t,
  apply is_empty.elim _ (s : S), assumption
end

lemma Profinite.is_zero_of_empty (S : Profinite.{u}) [is_empty S] :
  limits.is_zero S.condensed_free_pfpng :=
begin
  apply Condensed.is_zero_of_is_zero_obj,
  intros T,
  dsimp [Profinite.condensed_free_pfpng],
  dsimp [CompHausFiltPseuNormGrp.presheaf],
  apply is_zero_Ab,
  rintros ⟨⟨f,hf⟩⟩, ext t, change f t = 0,
  apply Profinite.free_pfpng_eq_zero_of_empty,
end

lemma category_theory.abelian.is_iso_of_mono_of_is_zero
  {A : Type*} [category A] [abelian A] {X Y : A} (f : X ⟶ Y) [mono f]
  (hY : limits.is_zero Y) : is_iso f :=
begin
  use 0, simp, split,
  rw ← cancel_mono f,
  apply hY.eq_of_tgt,
  apply hY.eq_of_tgt,
end

instance Profinite.epi_free'_to_condensed_free_pfpng_of_empty
  (S : Profinite.{u}) [is_empty S] :
  epi S.free'_to_condensed_free_pfpng :=
begin
  suffices : is_iso S.free'_to_condensed_free_pfpng,
  { resetI, apply_instance },
  apply category_theory.abelian.is_iso_of_mono_of_is_zero,
  apply Profinite.is_zero_of_empty,
end

-- Do a case split on `[nonempty S]` here.
instance Profinite.epi_free'_to_condensed_free_pfpng (S : Profinite.{u}) :
  epi S.free'_to_condensed_free_pfpng :=
begin
  by_cases hS : nonempty S, { resetI, apply_instance },
  simp only [not_nonempty_iff] at hS,
  resetI, apply_instance
end

instance Profinite.is_iso_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : is_iso S.free'_to_condensed_free_pfpng :=
is_iso_of_mono_of_epi _

def Profinite.free_to_pfpng (S : Profinite.{u}) :
  CondensedSet_to_Condensed_Ab.obj S.to_Condensed ⟶
  S.condensed_free_pfpng :=
(Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _).symm S.to_condensed_free_pfpng

attribute [simps hom_app] AddCommGroup.free_iso_free'

instance Profinite.is_iso_free_to_pfpng (S : Profinite.{u}) : is_iso S.free_to_pfpng :=
begin
  suffices : S.free_to_pfpng =
    (CondensedSet_to_Condensed_Ab_iso.app S.to_Condensed).hom ≫
    S.free'_to_condensed_free_pfpng,
  { rw this, apply_instance },
  rw [iso.app_hom],
  delta Profinite.free'_to_condensed_free_pfpng Profinite.free'_lift Profinite.free_to_pfpng
    CondensedSet_to_Condensed_Ab_iso Sheaf.adjunction
    Condensed_Ab_CondensedSet_adjunction Condensed_Ab_CondensedSet_adjunction',
  ext T : 4,
  dsimp only [adjunction.mk_of_hom_equiv_hom_equiv, functor.map_iso_hom, quiver.hom.forget_Ab,
    Sheaf.hom.comp_val, Condensed_Ab_to_CondensedSet_map, Sheaf.compose_equiv_symm_apply_val,
    presheaf_to_Sheaf_map_val, nat_trans.comp_app,
    iso_whisker_left_hom, iso_whisker_right_hom, whisker_left_app, whisker_right_app],
  rw [← nat_trans.comp_app, sheafify_map_sheafify_lift],
  congr' 4, clear T,
  ext T : 2,
  dsimp only [whiskering_right_map_app_app, whiskering_right_obj_map, nat_trans.comp_app,
    adjunction.whisker_right, adjunction.mk_of_unit_counit_hom_equiv_symm_apply,
    whisker_left_app, whisker_right_app,
    functor.associator_hom_app, functor.right_unitor_hom_app],
  erw [category.id_comp, category.id_comp, category.comp_id, category.comp_id],
  rw [← nat_trans.naturality_assoc],
  congr' 1,
  dsimp only [AddCommGroup.adj, AddCommGroup.adj', adjunction.mk_of_hom_equiv_hom_equiv,
    adjunction.of_nat_iso_left, adjunction.mk_of_hom_equiv_counit_app,
    equiv.inv_fun_as_coe, equiv.symm_trans_apply, iso.symm_hom,
    adjunction.equiv_homset_left_of_nat_iso_symm_apply],
  simp only [equiv.symm_symm],
  erw [← category.assoc, ← nat_trans.comp_app, iso.hom_inv_id, nat_trans.id_app,
    category.id_comp],
end

lemma free_pfpng_profinite_natural_map_aux (S T : Profinite.{u}) (f : S ⟶ T) :
  f ≫ T.to_free_pfpng = S.to_free_pfpng ≫
    (ProFiltPseuNormGrp₁.level.obj 1).map
    ((Profinite.extend free_pfpng_functor).map f) :=
begin
  apply (limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj 1)
   (limits.limit.is_limit _)).hom_ext,
  intros W, dsimp [Profinite.to_free_pfpng,
    Profinite.free_pfpng_level_iso, limits.is_limit.cone_point_unique_up_to_iso,
    limits.is_limit.map],
  simp only [category.assoc],
  erw (limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj 1)
    (limits.limit.is_limit (T.fintype_diagram ⋙ free_pfpng_functor))).fac,
  erw limits.limit.lift_π,
  swap, apply_instance,
  simp only [← functor.map_comp, limits.limit.lift_π],
  dsimp [Profinite.change_cone],
  simp only [functor.map_comp],
  erw (limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj 1)
    (limits.limit.is_limit (S.fintype_diagram ⋙ free_pfpng_functor))).fac_assoc,
  erw limits.limit.lift_π_assoc,
  ext, dsimp [Profinite.as_limit_cone, Fintype.free_pfpng_unit, free_pfpng.map,
    ProFiltPseuNormGrp₁.level],
  rcases x with ⟨x⟩,
  simp only [finset.filter_congr_decidable,
    int.nat_cast_eq_coe_nat],
  erw [finset.sum_filter, finset.sum_ite, finset.sum_ite],
  simp only [finset.filter_congr_decidable, finset.sum_const,
    nat.smul_one_eq_coe, int.nat_cast_eq_coe_nat, finset.sum_const_zero,
    add_zero],
  rw finset.filter_filter,
  split_ifs,
  { symmetry, norm_cast, rw finset.card_eq_one,
    use (W.comap f.2).proj a,
    rw finset.eq_singleton_iff_nonempty_unique_mem,
    split,
    { rw finset.filter_nonempty_iff,
      use (W.comap f.2).proj a,
      refine ⟨finset.mem_univ _, h, rfl⟩ },
    { rintros ⟨q⟩ hq,
      simp only [finset.mem_filter, finset.mem_univ, true_and] at hq,
      erw hq.2 } },
  { symmetry, norm_cast,
    simp only [finset.card_eq_zero],
    rw finset.filter_eq_empty_iff,
    rintros ⟨q⟩ -, push_neg, intros hh,
    rw ← hh at h,
    erw discrete_quotient.map_proj_apply at h,
    contrapose! h,
    let e : (W.comap f.2) → W := discrete_quotient.map (le_refl _),
    apply_fun e at h, exact h },
end

def free_pfpng_profinite_natural_map :
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab ⟶
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
  CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
  CompHausFiltPseuNormGrp.to_Condensed :=
{ app := λ X, X.free_to_pfpng,
  naturality' := λ S T f, begin
    -- we should be able to precompose with the natural map `S.to_Condensed ⟶ S.free'`
    -- how do we do that?
    -- Answer: use `adjunction.hom_equiv`.
    dsimp only [functor.comp_map],
    dsimp only [Profinite.free_to_pfpng],
    apply_fun (Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _),
    simp only [adjunction.hom_equiv_unit, adjunction.hom_equiv_counit, functor.map_comp],
    simp only [nat_trans.naturality, category.assoc, nat_trans.naturality_assoc],
    dsimp only [Profinite.condensed_free_pfpng],
    have := Condensed_Ab_CondensedSet_adjunction.unit.naturality
      (Profinite_to_Condensed.map f),
    dsimp only [functor.comp_map] at this,
    slice_lhs 1 2 { rw ← this }, clear this,
    dsimp only [functor.id_map], simp only [category.assoc],
    have := Condensed_Ab_CondensedSet_adjunction.unit.naturality
      S.to_condensed_free_pfpng,
    dsimp only [functor.comp_map] at this,
    slice_rhs 1 2 { erw ← this }, clear this,
    dsimp only [functor.id_map], simp only [category.assoc],
    have := Condensed_Ab_CondensedSet_adjunction.right_triangle_components,
    slice_rhs 2 3 { erw this }, clear this,
    erw category.id_comp,
    slice_lhs 2 3 { erw ← nat_trans.naturality },
    simp only [functor.id_map, category.assoc],
    have := Condensed_Ab_CondensedSet_adjunction.right_triangle_components,
    slice_lhs 3 4 { rw this }, clear this,
    erw category.comp_id,
    ext W ⟨t⟩ : 7, change W.unop ⟶ S at t,

    dsimp [Profinite.to_condensed_free_pfpng,
      CompHausFiltPseuNormGrp.level_Condensed_diagram_cocone,
      Ab.ulift, Profinite.to_free_pfpng_level],
    erw ← comp_apply,
    erw ← comp_apply,
    erw ← comp_apply,
    rw free_pfpng_profinite_natural_map_aux _ _ f, refl,
  end }

instance free_pfpng_profinite_natural_map_is_iso :
  is_iso free_pfpng_profinite_natural_map :=
begin
  apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
  intros X,
  apply X.is_iso_free_to_pfpng,
end

def free_pfpng_profinite_iso_aux :
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) ≅
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
    CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
    CompHausFiltPseuNormGrp.to_Condensed :=
nat_iso.of_components
(λ X, Sheaf.iso.mk _ _ $ begin
  dsimp [condensify],
  -- (AT) Use the fact that `ProFiltPseuNormGrp₁.to_CHFPNG₁` preserves limits.
  sorry
end)
sorry

/-- Prop 2.1 of Analytic.pdf -/
def free_pfpng_profinite_iso :
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) ≅
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab :=
free_pfpng_profinite_iso_aux ≪≫ (as_iso free_pfpng_profinite_natural_map).symm

.

-- #check Condensed_Ab_CondensedSet_adjunction
