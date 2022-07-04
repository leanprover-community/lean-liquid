import pseudo_normed_group.FP2
import condensed.adjunctions
import free_pfpng.acyclic
import for_mathlib.derived.ext_coproducts
import for_mathlib.derived.example
import breen_deligne.eval2
import system_of_complexes.shift_sub_id
import for_mathlib.AddCommGroup.explicit_products
import for_mathlib.free_abelian_group2

noncomputable theory

open_locale nnreal

universe u

open category_theory category_theory.limits breen_deligne

section step1

variables (r' : ℝ≥0)
variables (BD : breen_deligne.data) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

abbreviation freeCond := Profinite_to_Condensed.{u} ⋙ CondensedSet_to_Condensed_Ab

def QprimeFP_nat : ℝ≥0 ⥤ chain_complex (Condensed.{u} Ab.{u+1}) ℕ :=
FPsystem r' BD ⟨M⟩ κ ⋙ (freeCond.{u}.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _

def QprimeFP_int : ℝ≥0 ⥤ cochain_complex (Condensed.{u} Ab.{u+1}) ℤ :=
QprimeFP_nat r' BD κ M ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up

def QprimeFP : ℝ≥0 ⥤ bounded_homotopy_category (Condensed.{u} Ab.{u+1}) :=
QprimeFP_nat r' BD κ M ⋙ chain_complex.to_bounded_homotopy_category

end step1

section step2

variables {r' : ℝ≥0}
variables (BD : breen_deligne.package) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

abbreviation freeCond' := Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab

def ProFiltPseuNormGrpWithTinv₁.to_Condensed : Condensed.{u} Ab.{u+1} :=
(PFPNGT₁_to_CHFPNG₁ₑₗ r' ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u} ⋙
  CompHausFiltPseuNormGrp.to_Condensed.{u}).obj M

-- move me
/-- `Tinv : M → M` as hom of condensed abelian groups -/
def _root_.ProFiltPseuNormGrpWithTinv₁.Tinv_cond : M.to_Condensed ⟶ M.to_Condensed :=
(CompHausFiltPseuNormGrp.to_Condensed.{u}).map
  profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv

local attribute [instance] type_pow

set_option pp.universes true

def QprimeFP_incl_aux'' (c : ℝ≥0) (n : ℕ) (M : ProFiltPseuNormGrpWithTinv.{u} r') (i : fin n) :
  (FiltrationPow r' c n).obj M ⟶ ((Filtration r').obj c).obj M :=
((Filtration r').obj c).map $
  profinitely_filtered_pseudo_normed_group_with_Tinv.pi_proj _ _ i

def QprimeFP_incl_aux'
  (c : ℝ≥0) (n : ℕ) (i : (fin n)) (S : Profinite.{u}ᵒᵖ) :
  ulift_functor.{u+1 u}.obj (opposite.unop.{u+2} S ⟶ pseudo_normed_group.filtration_obj.{u} (M ^ n) c) ⟶
  ulift_functor.{u+1 u}.obj ((CompHausFiltPseuNormGrp.of.{u} ↥((PFPNGT₁_to_PFPNG₁ₑₗ.{u} r').obj M)).presheaf (opposite.unop.{u+2} S)) :=
ulift_functor.map $ λ f, ⟨subtype.val ∘ QprimeFP_incl_aux'' c n ⟨M⟩ i ∘ f,
  by refine ⟨_, _, continuous.comp _ _, rfl⟩; apply continuous_map.continuous⟩

-- move me
instance : preserves_limits (Condensed_Ab_to_CondensedSet.{u}) :=
adjunction.right_adjoint_preserves_limits Condensed_Ab_CondensedSet_adjunction

-- move me
instance : preserves_limits CondensedSet_to_presheaf :=
adjunction.right_adjoint_preserves_limits CondensedSet_presheaf_adjunction

universe v

lemma _root_.Ab.ulift_map_apply {A B : Ab.{u}} (f : A ⟶ B) :
  ⇑(Ab.ulift.{v}.map f) = ulift_functor.map f :=
by { ext, refl }

-- def QprimeFP_incl_aux_foo (c : ℝ≥0) (n : ℕ) :
--   (pseudo_normed_group.filtration_obj (M ^ n) c).to_Condensed ⟶
--   (Condensed_Ab_to_CondensedSet.obj (⨁ λ (i : ulift (fin n)), M.to_Condensed)) :=
-- begin
--   let x := biproduct.is_bilimit (λ (i : ulift (fin n)), M.to_Condensed),
--   let y := is_bilimit_of_preserves Condensed_Ab_to_presheaf x,
--   refine ⟨y.is_limit.lift ⟨_, ⟨λ i, ⟨_, _⟩, _⟩⟩⟩,
--   { refine QprimeFP_incl_aux' _ _ _ i.down, },
--   { intros S T f,
--     dsimp [QprimeFP_incl_aux', ProFiltPseuNormGrpWithTinv₁.to_Condensed],
--     rw [← ulift_functor.map_comp, Ab.ulift_map_apply, ← ulift_functor.map_comp],
--     congr' 1, },
--   { clear y x,
--     rintros ⟨i⟩ ⟨j⟩ ⟨⟨⟨⟩⟩⟩,
--     ext S : 2,
--     dsimp [QprimeFP_incl_aux', ProFiltPseuNormGrpWithTinv₁.to_Condensed],
--     simp only [discrete.functor_map_id, category.id_comp],
--     symmetry, apply category.comp_id, }
-- end

def QprimeFP_incl_aux (c : ℝ≥0) (n : ℕ) :
  (pseudo_normed_group.filtration_obj (M ^ n) c).to_Condensed ⟶
  (Condensed_Ab_to_CondensedSet.obj (⨁ λ (i : ulift (fin n)), M.to_Condensed)) :=
begin
  let x := biproduct.is_limit (λ (i : ulift (fin n)), M.to_Condensed),
  let y := is_limit_of_preserves (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf) x,
  refine ⟨y.lift ⟨_, ⟨λ i, ⟨_, _⟩, _⟩⟩⟩,
  { refine QprimeFP_incl_aux' _ _ _ i.down, },
  { intros S T f,
    dsimp [QprimeFP_incl_aux', ProFiltPseuNormGrpWithTinv₁.to_Condensed],
    rw [← ulift_functor.map_comp, Ab.ulift_map_apply, ← ulift_functor.map_comp],
    congr' 1, },
  { clear y x,
    rintros ⟨i⟩ ⟨j⟩ ⟨⟨⟨⟩⟩⟩,
    ext S : 2,
    dsimp [QprimeFP_incl_aux', ProFiltPseuNormGrpWithTinv₁.to_Condensed],
    simp only [discrete.functor_map_id, category.id_comp],
    symmetry, apply category.comp_id, }
end
.

set_option pp.universes false

lemma lift_app {C 𝓐 ι : Type*} [category C] [category 𝓐] [preadditive 𝓐]
  {F G : C ⥤ 𝓐} (f : ι → (F ⟶ G)) (x) (T) :
  (free_abelian_group.lift f x).app T = free_abelian_group.lift (λ i, (f i).app T) x :=
begin
  simp only [← nat_trans.app_hom_apply, ← add_monoid_hom.comp_apply],
  congr' 1, clear x, ext x,
  simp only [add_monoid_hom.coe_comp, function.comp_app, free_abelian_group.lift.of],
end

lemma map_FreeAb_comp_map {X Y Z : Type*} [category X] [category Y] [category Z]
  (F : X ⥤ Y) (G : Y ⥤ Z) {α β : FreeAb X} (f : α ⟶ β) :
  (F ⋙ G).map_FreeAb.map f = G.map_FreeAb.map (F.map_FreeAb.map f) :=
begin
  dsimp only [functor.map_FreeAb, functor.comp_map],
  rw [← add_monoid_hom.comp_apply], congr' 1, clear f,
  ext f,
  simp only [free_abelian_group.map_of_apply, functor.comp_map, add_monoid_hom.coe_comp, function.comp_app],
end

open category_theory.preadditive
open_locale big_operators

lemma biproduct.desc_eq_sum {𝓐 ι : Type*} [category 𝓐] [abelian 𝓐] [fintype ι] [decidable_eq ι]
  (M : ι → 𝓐) (X : 𝓐) (f : Π i, M i ⟶ X) :
  biproduct.desc f = ∑ i : ι, (biproduct.π _ _) ≫ (f i) :=
begin
  ext i, simp only [biproduct.ι_desc, comp_sum],
  rw finset.sum_eq_single_of_mem i (finset.mem_univ _),
  { rw [biproduct.ι_π_assoc, dif_pos rfl, eq_to_hom_refl, category.id_comp], },
  { rintro j - hj, rw [biproduct.ι_π_ne_assoc, zero_comp], exact hj.symm }
end

instance group_of_sections (A B : Condensed.{u} Ab.{u+1}) (S : Profinite.{u}ᵒᵖ) :
  add_comm_group
  (((Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).obj A).obj S ⟶
    ((Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).obj B).obj S) :=
-- generated using `show_term {dsimp, apply_instance}` with `pp.implicit true`
@pi.add_comm_group
  ↥((@Sheaf.val Profinite Profinite.category proetale_topology Ab AddCommGroup.large_category A).obj S)
  (λ (ᾰ : ↥((@Sheaf.val Profinite Profinite.category proetale_topology Ab AddCommGroup.large_category A).obj S)),
     ↥((@Sheaf.val Profinite Profinite.category proetale_topology Ab AddCommGroup.large_category B).obj S))
  (λ (i : ↥((@Sheaf.val Profinite Profinite.category proetale_topology Ab AddCommGroup.large_category A).obj S)),
     AddCommGroup.add_comm_group_instance
       ((@Sheaf.val Profinite Profinite.category proetale_topology Ab AddCommGroup.large_category B).obj S))

instance group_of_homs (X) (A : Condensed.{u} Ab.{u+1}) :
  add_comm_group (X ⟶ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).obj A) :=
sorry

lemma QprimeFP_incl_aux1 {A B : Condensed.{u} Ab.{u+1}} {ι : Type*} {X}
  (f : X ⟶ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).obj A)
  (s : finset ι) (n : ι → ℤ) (g : ι → (A ⟶ B)) :
  f ≫ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map (∑ i in s, n i • g i) =
  ∑ i in s, n i • (f ≫ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map (g i)) :=
begin
  sorry
end

def QprimeFP_incl (c : ℝ≥0) :
  (QprimeFP_int r' BD.data κ M).obj c ⟶
  (BD.eval' freeCond').obj M.to_Condensed :=
(homological_complex.embed complex_shape.embedding.nat_down_int_up).map
{ f := λ n, CondensedSet_to_Condensed_Ab.map $ QprimeFP_incl_aux _ _ _,
  comm' := begin
    rintro _ n (rfl : _ = _),
    rw [package.eval_functor_obj_d],
    dsimp only [universal_map.eval_Pow],
    dsimp only [QprimeFP_nat, FPsystem, functor.comp_obj, functor.map_homological_complex_obj_d],
    rw [chain_complex.of_d],
    delta freeCond freeCond',
    rw [functor.comp_map, map_FreeAb_comp_map, lift_app],
    dsimp only [FreeAb.eval, functor.map_FreeAb, FPsystem.d,
      universal_map.eval_FP2],
    simp only [whisker_right_app, free_abelian_group.lift_map, function.comp.left_id,
      nat_trans.app_sum, map_sum, basic_universal_map.eval_Pow_app,
      nat_trans.app_zsmul, basic_universal_map.eval_FP2, map_zsmul],
    dsimp only [FreeAb.of_functor],
    simp only [free_abelian_group.lift.of, function.comp_app],
    rw [free_abelian_group.lift_eq_sum, comp_sum, sum_comp, ← finset.sum_coe_sort],
    apply finset.sum_congr rfl,
    rintro t -,
    rw [comp_zsmul, zsmul_comp], refine congr_arg2 _ rfl _,
    rw [functor.comp_map, ← functor.map_comp, ← functor.map_comp],
    congr' 1,
    ext1,
    let x := λ n, biproduct.is_limit (λ (i : ulift (fin (BD.data.X n))), M.to_Condensed),
    let y := λ n, is_limit_of_preserves (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf) (x n),
    apply (y _).hom_ext, intro j,
    rw [← CondensedSet_to_presheaf_map, ← CondensedSet_to_presheaf_map, functor.map_comp,
      ← functor.comp_map, category.assoc, functor.map_comp, category.assoc],
    erw [← functor.map_comp, biproduct.matrix_π],
    dsimp only [QprimeFP_incl_aux, CondensedSet_to_presheaf_map],
    rw (y _).fac,
    simp only [biproduct.desc_eq_sum, comp_zsmul, category.comp_id],
    rw [QprimeFP_incl_aux1],
    have help : ∀ n i,
      ((Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map_cone
        (biproduct.bicone (λ (i : ulift (fin (BD.data.X n))), M.to_Condensed)).to_cone).π.app i =
      (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map
        (biproduct.π (λ (i : ulift (fin (BD.data.X n))), M.to_Condensed) i),
    { intros, refl },
    simp only [← help, (y _).fac],
    dsimp only [basic_universal_map.eval_FP, Profinite_to_Condensed_map_val,
      basic_universal_map.eval_png₀],
    ext S : 2,
    -- dsimp,
    sorry,
  end }

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

def QprimeFP_sigma_proj :
  ∐ (λ k, (QprimeFP_int r' BD.data κ M).obj (ι k)) ⟶
  (BD.eval' freeCond').obj M.to_Condensed :=
sigma.desc $ λ n, QprimeFP_incl BD κ M _

instance QprimeFP.uniformly_bounded :
  bounded_homotopy_category.uniformly_bounded (λ k, (QprimeFP r' BD.data κ M).obj (ι k)) :=
begin
  use 1, intro k, apply chain_complex.bounded_by_one,
end

end step2

section step3
open bounded_homotopy_category

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)
variables {C : Type*} [category C] [preadditive C]
variables (A B : ℝ≥0 ⥤ C)
variables [has_coproduct (λ (k : ulift ℕ), A.obj (ι k))]
variables [has_coproduct (λ (k : ulift ℕ), B.obj (ι k))]

def sigma_shift_cone (c : cofan (λ k, A.obj (ι k))) :
  cofan (λ k, A.obj (ι k)) :=
{ X := c.X,
  ι := discrete.nat_trans $ λ (j:ulift ℕ),
    A.map (hom_of_le $ hι $ (by { cases j, apply nat.le_succ } : j ≤ ⟨j.down+1⟩)) ≫ c.ι.app _ }

def sigma_shift' (c : cofan (λ k, A.obj (ι k))) (hc : is_colimit c) :
  c.X ⟶ (sigma_shift_cone ι hι A c).X := hc.desc _

def sigma_shift : ∐ (λ k, A.obj (ι k)) ⟶ ∐ (λ k, A.obj (ι k)) :=
sigma_shift' _ hι _ _ (colimit.is_colimit _)

def QprimeFP.shift_sub_id : ∐ (λ k, A.obj (ι k)) ⟶ ∐ (λ k, A.obj (ι k)) :=
sigma_shift _ hι _ - 𝟙 _

variables {A B}

def sigma_map (f : A ⟶ B) : ∐ (λ k, A.obj (ι k)) ⟶ ∐ (λ k, B.obj (ι k)) :=
sigma.desc $ λ k, f.app _ ≫ sigma.ι _ k

end step3

section step4

variables {r' : ℝ≥0}
variables (BD : breen_deligne.package) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

open opposite category_theory.preadditive

lemma mono_iff_ExtrDisc {A B : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) :
  mono f ↔ ∀ S : ExtrDisc, mono (f.1.app $ ExtrDisc_to_Profinite.op.obj (op S)) :=
begin
  split,
  { intros H S,
    erw (abelian.tfae_mono (A.val.obj (op S.val)) (f.val.app (op S.val))).out 0 2,
    erw (abelian.tfae_mono A f).out 0 2 at H,
    rw Condensed.exact_iff_ExtrDisc at H,
    apply H, },
  { intro H,
    apply exact.mono_of_exact_zero_left, swap, exact A,
    rw Condensed.exact_iff_ExtrDisc,
    intro S, specialize H S,
    show exact 0 _,
    erw (abelian.tfae_mono (A.val.obj (op S.val)) (f.val.app (op S.val))).out 2 0,
    exact H, }
end

lemma short_exact_iff_ExtrDisc {A B C : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) (g : B ⟶ C) :
  short_exact f g ↔ ∀ S : ExtrDisc, short_exact
      (f.1.app $ ExtrDisc_to_Profinite.op.obj (op S))
      (g.1.app $ ExtrDisc_to_Profinite.op.obj (op S)) :=
begin
  split,
  { intros H S,
    apply_with short_exact.mk {instances:=ff},
    { revert S, rw ← mono_iff_ExtrDisc, exact H.mono, },
    { rw AddCommGroup.epi_iff_surjective,
      revert S, erw ← is_epi_iff_forall_surjective, exact H.epi, },
    { revert S, rw ← Condensed.exact_iff_ExtrDisc, exact H.exact } },
  { intro H,
    apply_with short_exact.mk {instances:=ff},
    { rw mono_iff_ExtrDisc, intro S, exact (H S).mono, },
    { simp only [is_epi_iff_forall_surjective, ← AddCommGroup.epi_iff_surjective],
      intro S, exact (H S).epi, },
    { rw Condensed.exact_iff_ExtrDisc, intro S, exact (H S).exact } }
end
.

open_locale classical

set_option pp.universes true

.

def coproduct_eval_iso
  {α : Type (u+1)} (X : α → homological_complex (Condensed.{u} Ab.{u+1}) (complex_shape.up ℤ))
  (n : ℤ) (T : ExtrDisc.{u}) :
  ((∐ X).X n).val.obj (op T.val) ≅
  AddCommGroup.of (direct_sum α (λ a, ((X a).X n).val.obj (op T.val))) :=
begin
  refine preserves_colimit_iso
    ((homological_complex.eval (Condensed.{u} Ab.{u+1}) (complex_shape.up ℤ) n
    ⋙ Condensed.evaluation Ab.{u+1} T.val)) _ ≪≫ _,
  refine _ ≪≫ (colimit.is_colimit $ discrete.functor
    (λ a, ((X a).X n).val.obj (op T.val))).cocone_point_unique_up_to_iso
    (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} (λ a, ((X a).X n).val.obj (op T.val))),
  refine has_colimit.iso_of_nat_iso (discrete.nat_iso _),
  intros i, exact iso.refl _,
end

lemma sigma_ι_coproduct_eval_iso
  {α : Type (u+1)} (X : α → homological_complex (Condensed.{u} Ab.{u+1}) (complex_shape.up ℤ))
  (n : ℤ) (T : ExtrDisc.{u}) (a : α) :
  ((sigma.ι X a : X a ⟶ _).f n).val.app (op T.val) ≫
  (coproduct_eval_iso _ _ _).hom =
  direct_sum.of ((λ a, ((X a).X n).val.obj (op T.val))) a :=
begin
  dsimp only [coproduct_eval_iso],
  erw (is_colimit_of_preserves (homological_complex.eval.{u+1 u+2 0}
    (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ) n ⋙
    Condensed.evaluation.{u+2 u+1 u} Ab.{u+1} T.val) _).fac_assoc,
  dsimp,
  erw colimit.ι_desc_assoc,
  dsimp, simpa only [category.id_comp, colimit.comp_cocone_point_unique_up_to_iso_hom],
end

lemma QprimeFP.mono (n : ℤ) :
  mono ((QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD.data κ M)).f n) :=
begin
  rw mono_iff_ExtrDisc, intros T,
  let e : ((∐ λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X n).val.obj
    (op T.val) ≅ _ := coproduct_eval_iso _ _ _,
  let Q := QprimeFP_int r' BD.data κ M,
  let φ : ulift.{u+1} ℕ → Ab.{u+1} := λ k, ((Q.obj (ι k)).X n).val.obj (op T.val),
  let D := AddCommGroup.direct_sum_cofan.{u+1 u+1} φ,
  let hD := AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} φ,
  let g : D.X ⟶ D.X := sigma_shift'.{u u+2 u+1} _ hι (Q ⋙ (homological_complex.eval
    (Condensed.{u} Ab.{u+1}) (complex_shape.up ℤ) n) ⋙ Condensed.evaluation _ T.val) D hD,
  let f := _, change mono f,
  have hf : f = e.hom ≫ (g - 𝟙 _) ≫ e.inv,
  { rw [← category.assoc, iso.eq_comp_inv],
    dsimp [f, QprimeFP.shift_sub_id],
    change (_ - _) ≫ _ = _,
    simp only [comp_sub, sub_comp, category.id_comp, category.comp_id, Sheaf.hom.id_val,
      nat_trans.id_app], congr' 1,
    refine ((is_colimit_of_preserves (homological_complex.eval.{u+1 u+2 0}
      (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ) n ⋙
      Condensed.evaluation.{u+2 u+1 u} Ab.{u+1} T.val) (colimit.is_colimit _))).hom_ext (λ j, _),
    dsimp [sigma_shift],
    slice_lhs 1 2
    { erw [← nat_trans.comp_app, ← Sheaf.hom.comp_val, ← homological_complex.comp_f,
        colimit.ι_desc] },
    slice_rhs 1 2
    { erw sigma_ι_coproduct_eval_iso },
    dsimp [sigma_shift_cone],
    rw category.assoc,
    slice_lhs 2 3
    { erw sigma_ι_coproduct_eval_iso },
    erw hD.fac, refl },
  suffices : mono (g - 𝟙 _),
  { rw hf,
    apply_with mono_comp { instances := ff },
    apply_instance,
    apply_with mono_comp { instances := ff },
    exact this,
    apply_instance },
  rw [AddCommGroup.mono_iff_injective, injective_iff_map_eq_zero],
  intros x hx,
  erw [sub_eq_zero, id_apply] at hx,
  ext ⟨i⟩,
  classical,
  induction i with i IH,
  { rw ← hx,
    dsimp [g, sigma_shift', sigma_shift_cone, hD, AddCommGroup.is_colimit_direct_sum_cofan,
      AddCommGroup.direct_sum_desc, discrete.nat_trans, direct_sum.to_add_monoid],
    rw [dfinsupp.sum_add_hom_apply, dfinsupp.sum_apply],
    apply finset.sum_eq_zero,
    rintro ⟨j⟩ -,
    convert dif_neg _,
    rw [finset.mem_singleton],
    intro H, rw ulift.ext_iff at H, revert H, apply nat.no_confusion, },
  { rw ← hx,
    classical,
    dsimp [g, sigma_shift', sigma_shift_cone, hD, AddCommGroup.is_colimit_direct_sum_cofan,
      AddCommGroup.direct_sum_desc, discrete.nat_trans, direct_sum.to_add_monoid],
    rw [dfinsupp.sum_add_hom_apply, dfinsupp.sum_apply],
    rw dfinsupp.zero_apply at IH,
    convert finset.sum_eq_single (ulift.up $ i) _ _,
    { rw [IH, add_monoid_hom.map_zero, dfinsupp.zero_apply], },
    { rintro ⟨j⟩ - hj, convert dif_neg _, rw [finset.mem_singleton],
      intro H, apply hj, rw ulift.ext_iff at H ⊢, change i+1 = j+1 at H,
      change j = i, linarith only [H] },
    { intro, rw [IH, add_monoid_hom.map_zero, dfinsupp.zero_apply], }, },
  recover, all_goals { classical; apply_instance }
end
.

lemma QprimeFP.short_exact (n : ℤ) :
  short_exact
    ((QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD.data κ M)).f n)
    ((QprimeFP_sigma_proj BD κ M ι).f n) :=
begin
  apply_with short_exact.mk {instances:=ff},
  { apply QprimeFP.mono },
  { rw is_epi_iff_forall_surjective,
    intro S,
    sorry },
  { rw Condensed.exact_iff_ExtrDisc,
    intro S,
    sorry },
end

end step4

section step5

variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)]
variables (BD : breen_deligne.data)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

def QprimeFP_nat.Tinv [∀ c n, fact (κ c n ≤ r' * κ₂ c n)] :
  (QprimeFP_nat r' BD κ M) ⟶ (QprimeFP_nat r' BD κ₂ M) :=
whisker_right (FPsystem.Tinv.{u} r' BD ⟨M⟩ _ _) _

def QprimeFP_int.Tinv [∀ c n, fact (κ c n ≤ r' * κ₂ c n)] :
  (QprimeFP_int r' BD κ M) ⟶ (QprimeFP_int r' BD κ₂ M) :=
whisker_right (QprimeFP_nat.Tinv _ _ _ _)
  (homological_complex.embed complex_shape.embedding.nat_down_int_up)

def QprimeFP.Tinv [∀ c n, fact (κ c n ≤ r' * κ₂ c n)] :
  (QprimeFP r' BD κ M) ⟶ (QprimeFP r' BD κ₂ M) :=
whisker_right (QprimeFP_nat.Tinv _ _ _ _) chain_complex.to_bounded_homotopy_category

/-- The natural inclusion map -/
def QprimeFP_nat.ι [∀ c n, fact (κ c n ≤ κ₂ c n)] :
  (QprimeFP_nat r' BD κ M) ⟶ (QprimeFP_nat r' BD κ₂ M) :=
whisker_right (FPsystem.res r' BD ⟨M⟩ _ _) _

/-- The natural inclusion map -/
def QprimeFP_int.ι [∀ c n, fact (κ c n ≤ κ₂ c n)] :
  (QprimeFP_int r' BD κ M) ⟶ (QprimeFP_int r' BD κ₂ M) :=
whisker_right (QprimeFP_nat.ι _ _ _ _)
  (homological_complex.embed complex_shape.embedding.nat_down_int_up)

/-- The natural inclusion map -/
def QprimeFP.ι [∀ c n, fact (κ c n ≤ κ₂ c n)] :
  (QprimeFP r' BD κ M) ⟶ (QprimeFP r' BD κ₂ M) :=
whisker_right (QprimeFP_nat.ι _ _ _ _) chain_complex.to_bounded_homotopy_category

open category_theory.preadditive

lemma commsq_shift_sub_id_Tinv [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ r' * κ c n)] :
  commsq (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD κ₂ M))
  (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.Tinv BD κ₂ κ M))
  (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.Tinv BD κ₂ κ M))
  (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD κ M)) :=
commsq.of_eq begin
  delta QprimeFP.shift_sub_id,
  rw [sub_comp, comp_sub, category.id_comp, category.comp_id],
  refine congr_arg2 _ _ rfl,
  apply colimit.hom_ext, intro j,
  dsimp [sigma_shift, sigma_shift', sigma_shift_cone],
  simp only [sigma_shift, sigma_shift', sigma_shift_cone, sigma_map, colimit.ι_desc_assoc,
    colimit.ι_desc, cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc,
    discrete.nat_trans_app],
end

lemma commsq_shift_sub_id_ι [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ κ c n)] :
  commsq (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD κ₂ M))
  (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.ι BD κ₂ κ M))
  (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.ι BD κ₂ κ M))
  (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD κ M)) :=
commsq.of_eq begin
  delta QprimeFP.shift_sub_id,
  rw [sub_comp, comp_sub, category.id_comp, category.comp_id],
  refine congr_arg2 _ _ rfl,
  apply colimit.hom_ext, intro j,
  dsimp [sigma_shift, sigma_shift', sigma_shift_cone],
  simp only [sigma_shift, sigma_shift', sigma_shift_cone, sigma_map, colimit.ι_desc_assoc,
    colimit.ι_desc, cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc,
    discrete.nat_trans_app],
end

end step5

section step6

variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)]
variables (BD : breen_deligne.package)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.data.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

open category_theory.preadditive

-- lemma commsq_sigma_proj_Tinv' (j) (n : ℕ) [fact (κ₂ (ι j) n ≤ r' * κ (ι j) n)] :
-- QprimeFP_incl_aux M (κ₂ (ι j) n) (BD.data.X n) ≫
--     Condensed_Ab_to_CondensedSet.map (biproduct.map (λ (i : ulift (fin (BD.data.X n))), M.Tinv_cond)) =
--   Profinite_to_Condensed.map
--       ((FiltrationPow.Tinv r' (κ₂ (ι j) n) (κ (ι j) n) (BD.data.X n)).app ⟨M⟩) ≫
--     QprimeFP_incl_aux M (κ (ι j) n) (BD.data.X n) :=
-- by admit

lemma commsq_sigma_proj_Tinv [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ r' * κ c n)] :
  commsq (QprimeFP_sigma_proj BD κ₂ M ι) (sigma_map (λ (k : ulift ℕ), ι k)
    (QprimeFP_int.Tinv BD.data κ₂ κ M))
  ((BD.eval' freeCond').map M.Tinv_cond)
  (QprimeFP_sigma_proj BD κ M ι) :=
commsq.of_eq begin
  apply colimit.hom_ext, intro j,
  simp only [QprimeFP_sigma_proj, sigma_map, colimit.ι_desc_assoc, colimit.ι_desc,
    cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc],
  dsimp only [QprimeFP_incl, QprimeFP_int.Tinv, whisker_right_app,
    package.eval', functor.comp_map],
  rw [← functor.map_comp, ← functor.map_comp],
  refine congr_arg _ _,
  ext n : 2,
  dsimp only [homological_complex.comp_f, data.eval_functor, functor.comp_obj, functor.flip_obj_map,
    homological_complex.functor_eval_map_app_f, data.eval_functor'_obj_X_map, functor.comp_map,
    QprimeFP_nat.Tinv, whisker_right_app, functor.map_homological_complex_map_f],
  rw [map_FreeAb_comp_map],
  dsimp only [FreeAb.eval, functor.map_FreeAb, FPsystem.Tinv, FP2.Tinv_app,
    FreeAb.of_functor],
  simp only [free_abelian_group.lift_map, function.comp, function.comp.left_id],
  rw [free_abelian_group.lift.of],
  simp only [← functor.map_comp],
  congr' 1,
  sorry
end

lemma commsq_sigma_proj_ι [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ κ c n)] :
  commsq (QprimeFP_sigma_proj BD κ₂ M ι) (sigma_map (λ (k : ulift ℕ), ι k)
    (QprimeFP_int.ι BD.data κ₂ κ M)) (𝟙 _) (QprimeFP_sigma_proj BD κ M ι) :=
commsq.of_eq begin
  simp only [category.comp_id],
  apply colimit.hom_ext, intro j,
  simp only [QprimeFP_sigma_proj, sigma_map, colimit.ι_desc_assoc, colimit.ι_desc,
    cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc],
  sorry
end

end step6

-- variables (f : ℕ → ℝ≥0)
-- #check ∐ (λ i, (QprimeFP r' BD κ M).obj (f i))
