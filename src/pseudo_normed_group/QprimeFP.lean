import pseudo_normed_group.FP2
import condensed.adjunctions
import free_pfpng.acyclic
import for_mathlib.derived.ext_coproducts
import for_mathlib.derived.example
import breen_deligne.eval2
import system_of_complexes.shift_sub_id
import for_mathlib.AddCommGroup.explicit_products
import condensed.Qprime_isoms
import condensed.short_exact
import condensed.bd_ses
import condensed.filtered_colimits

noncomputable theory

open_locale nnreal

universe u

open category_theory category_theory.limits breen_deligne

def ProFiltPseuNormGrpWithTinv₁.to_CHFPNG {r'} (M : ProFiltPseuNormGrpWithTinv₁.{u} r') :
  CompHausFiltPseuNormGrp :=
(PFPNGT₁_to_CHFPNG₁ₑₗ r' ⋙ CHFPNG₁_to_CHFPNGₑₗ).obj M

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
  { refine QprimeFP_incl_aux' _ _ _ i.as.down, },
  { intros S T f,
    rcases i with ⟨⟨i⟩⟩,
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

instance group_of_sections (A : Condensed.{u} Ab.{u+1})
  (S : Profinite.{u}ᵒᵖ) :
  add_comm_group (((Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).obj A).obj S) :=
AddCommGroup.add_comm_group_instance
  ((@Sheaf.val Profinite Profinite.category proetale_topology Ab AddCommGroup.large_category A).obj S)

instance group_of_homs (X A : Type u) [add_comm_group A] :
  add_comm_group (X ⟶ A) :=
@pi.add_comm_group X _ _

instance ulift_functor_group (A : Type u) [add_comm_group A] :
  add_comm_group (ulift_functor.obj A) :=
ulift.add_comm_group

lemma QprimeFP_incl_aux3 {X A : Type u} [add_comm_group A] {ι : Type*}
  (s : finset ι) (n : ι → ℤ) (f : ι → (X ⟶ A)) :
  (∑ i in s, n i • (ulift_functor.{v}).map (f i)) = ulift_functor.map (∑ i in s, n i • (f i)) :=
begin
  let φ := add_monoid_hom.mk' (λ g : X ⟶ A, ulift_functor.{v}.map g) _,
  { show ∑ i in s, n i • φ (f i) = _, simp only [← φ.map_sum, ← φ.map_zsmul], refl },
  intros g₁ g₂, refl,
end

instance group_of_sheaf_homs (X) (A : Condensed.{u} Ab.{u+1}) :
  add_comm_group (X ⟶ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).obj A) :=
{ add := λ f g, ⟨λ S, f.app S + g.app S,
    by { intros S T φ, show X.map φ ≫ f.app T + X.map φ ≫ g.app T = _,
      simp only [nat_trans.naturality], ext1 x, symmetry,
      exact (A.val.map φ).map_add (f.app S x) (g.app S x) }⟩,
  add_assoc := by { intros, ext : 2, apply add_assoc },
  zero := ⟨λ S, 0, by { intros S T φ, ext1 x, symmetry, exact (A.val.map φ).map_zero }⟩,
  zero_add := by { intros, ext : 2, apply zero_add },
  add_zero := by { intros, ext : 2, apply add_zero },
  nsmul := λ n f, ⟨λ S, n • f.app S,
    by { intros S T φ, show n • (X.map φ ≫ f.app T) = _,
      simp only [nat_trans.naturality], ext1 x, symmetry,
      exact (A.val.map φ).map_nsmul (f.app S x) n }⟩,
  nsmul_zero' := by { intros, ext : 2, apply add_comm_group.nsmul_zero' },
  nsmul_succ' := by { intros, ext : 2, apply add_comm_group.nsmul_succ' },
  neg := λ f, ⟨λ S, -f.app S,
    by { intros S T φ, show -(X.map φ ≫ f.app T) = _,
      simp only [nat_trans.naturality], ext1 x, symmetry,
      exact (A.val.map φ).map_neg (f.app S x) }⟩,
  sub := λ f g, ⟨λ S, f.app S - g.app S,
    by { intros S T φ, show X.map φ ≫ f.app T - X.map φ ≫ g.app T = _,
      simp only [nat_trans.naturality], ext1 x, symmetry,
      exact (A.val.map φ).map_sub (f.app S x) (g.app S x) }⟩,
  sub_eq_add_neg := by { intros, ext : 2, apply sub_eq_add_neg },
  zsmul := λ n f, ⟨λ S, n • f.app S,
    by { intros S T φ, show n • (X.map φ ≫ f.app T) = _,
      simp only [nat_trans.naturality], ext1 x, symmetry,
      exact (A.val.map φ).map_zsmul (f.app S x) n }⟩,
  zsmul_zero' := by { intros, ext : 2, apply add_comm_group.zsmul_zero' },
  zsmul_succ' := by { intros, ext : 2, apply add_comm_group.zsmul_succ' },
  zsmul_neg' := by { intros, ext : 2, apply add_comm_group.zsmul_neg' },
  add_left_neg := by { intros, ext : 2, apply add_left_neg },
  add_comm := by { intros, ext : 2, apply add_comm } }

lemma QprimeFP_incl_aux1 {A B : Condensed.{u} Ab.{u+1}} {ι : Type*} {X}
  (f : X ⟶ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).obj A)
  (s : finset ι) (n : ι → ℤ) (g : ι → (A ⟶ B)) :
  f ≫ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map (∑ i in s, n i • g i) =
  ∑ i in s, n i • (f ≫ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map (g i)) :=
begin
  let φ := add_monoid_hom.mk' (λ g : A ⟶ B, f ≫ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map g) _,
  { show φ _ = _, simp only [φ.map_sum, φ.map_zsmul], refl },
  intros g₁ g₂, refl,
end

lemma QprimeFP_incl_aux2 {A : Condensed.{u} Ab.{u+1}} {ι : Type*} {X}
  (s : finset ι) (n : ι → ℤ)
  (f : ι → (X ⟶ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).obj A)) (S) :
  (∑ i in s, n i • f i).app S = ∑ i in s, n i • ((f i).app S) :=
begin
  let φ := add_monoid_hom.mk' (λ g : X ⟶ (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).obj A, nat_trans.app g S) _,
  { show φ _ = _, simp only [φ.map_sum, φ.map_zsmul], refl },
  intros g₁ g₂, refl,
end

-- move me
-- lemma _root_.comphaus_filtered_pseudo_normed_group_hom.coe_to_add_monoid_hom
--   {M N : Type*} [comphaus_filtered_pseudo_normed_group M] [comphaus_filtered_pseudo_normed_group N]
--   (f : comphaus_filtered_pseudo_normed_group_hom M N) :
--   ⇑f.to_add_monoid_hom = f := rfl

@[simps] def _root_.CompHausFiltPseuNormGrp.presheaf_incl
  (A : CompHausFiltPseuNormGrp.{u}) (S : Profinite.{u}) :
  CompHausFiltPseuNormGrp.presheaf A S →+ (S → A) :=
add_monoid_hom.mk' subtype.val $ λ _ _, rfl

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
    apply (y _).hom_ext, rintro ⟨j⟩,
    rw [← CondensedSet_to_presheaf_map, ← CondensedSet_to_presheaf_map, functor.map_comp,
      ← functor.comp_map, category.assoc, functor.map_comp, category.assoc],
    erw [← functor.map_comp, biproduct.matrix_π],
    dsimp only [QprimeFP_incl_aux, CondensedSet_to_presheaf_map],
    rw (y _).fac,
    simp only [biproduct.desc_eq_sum, comp_zsmul, category.comp_id],
    rw [QprimeFP_incl_aux1],
    have help : ∀ n i,
      ((Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map_cone
        (biproduct.bicone (λ (i : ulift (fin (BD.data.X n))), M.to_Condensed)).to_cone).π.app ⟨i⟩ =
      (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map
        (biproduct.π (λ (i : ulift (fin (BD.data.X n))), M.to_Condensed) i),
    { intros, refl },
    simp only [← help, (y _).fac], clear help,
    dsimp only [basic_universal_map.eval_FP, Profinite_to_Condensed_map_val,
      basic_universal_map.eval_png₀],
    ext S : 2,
    erw QprimeFP_incl_aux2,
    dsimp only [nat_trans.comp_app, whisker_right_app, QprimeFP_incl_aux'],
    rw [← ulift_functor.map_comp, types_comp, QprimeFP_incl_aux3],
    congr' 1,
    dsimp only [function.comp, yoneda_map_app, yoneda_obj_obj, chain_complex.of_X,
      Profinite.coe_comp_apply, continuous_map.coe_mk, QprimeFP_incl_aux''],
    ext f s, clear y x,
    dsimp only [subtype.coe_mk, Filtration_obj_map_to_fun, add_monoid_hom.mk'_apply,
      comphaus_filtered_pseudo_normed_group_with_Tinv_hom.level, pseudo_normed_group.level,
      profinitely_filtered_pseudo_normed_group_with_Tinv.pi_proj,
      comphaus_filtered_pseudo_normed_group_with_Tinv_hom.coe_mk,
      pi.eval_add_monoid_hom_apply, breen_deligne.basic_universal_map.eval_png₀,
      breen_deligne.basic_universal_map.eval_png,
      comphaus_filtered_pseudo_normed_group.pi_lift,
      comphaus_filtered_pseudo_normed_group_hom.coe_mk, add_monoid_hom.mk_to_pi_apply],
    simp only [← comphaus_filtered_pseudo_normed_group_hom.to_add_monoid_hom_hom_apply,
      add_monoid_hom.map_sum],
    rw [fintype.sum_apply, ← add_monoid_hom.eval_apply_apply, add_monoid_hom.map_sum,
      ← CompHausFiltPseuNormGrp.presheaf_incl_apply, add_monoid_hom.map_sum, fintype.sum_apply],
    rw [← equiv.ulift.{u+1 0}.sum_comp],
    refine finset.sum_congr rfl _,
    intros t ht, refl,
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

include hι

def sigma_shift_cone (c : cofan (λ k, A.obj (ι k))) :
  cofan (λ k, A.obj (ι k)) :=
{ X := c.X,
  ι := discrete.nat_trans $ λ ⟨(j: ulift ℕ)⟩,
        A.map (hom_of_le $ hι $ (by { cases j, apply nat.le_succ } : j ≤ ⟨j.down+1⟩)) ≫
          c.ι.app ⟨⟨j.down + 1⟩⟩ }

omit hι

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

open_locale classical

set_option pp.universes true

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

-- Move this!
instance CondensedSet_to_Condensed_Ab_preserves_colimits :
  preserves_colimits CondensedSet_to_Condensed_Ab.{u} :=
adjunction.left_adjoint_preserves_colimits Condensed_Ab_CondensedSet_adjunction

section ses_setup

local attribute [instance] type_pow

def Condensed_prod_val_iso {α : Type (u+1)} (X : α → CondensedSet.{u}) :
  (∏ X).val ≅ ∏ (λ i, (X i).val) :=
preserves_limit_iso CondensedSet_to_presheaf _ ≪≫
has_limit.iso_of_nat_iso (discrete.nat_iso $ λ p, iso.refl _)

@[simp, reassoc]
lemma Condensed_prod_val_iso_spec {α : Type (u+1)} (X : α → CondensedSet.{u}) (i : α) :
  (Condensed_prod_val_iso X).hom ≫ pi.π _ i =
  (pi.π X i : ∏ X ⟶ X i).val :=
begin
  dsimp [Condensed_prod_val_iso],
  simp only [category.assoc],
  erw limit.lift_π,
  dsimp,
  erw limit.lift_π_assoc,
  erw category.comp_id,
  refl,
end

@[simp, reassoc]
lemma Condensed_prod_val_iso_spec' {α : Type (u+1)} (X : α → CondensedSet.{u}) (i : α) :
  (Condensed_prod_val_iso X).inv ≫ (pi.π X i : ∏ X ⟶ X i).val = pi.π _ _ :=
by { rw iso.inv_comp_eq, rw Condensed_prod_val_iso_spec }

def functor_prod_eval_iso {α : Type (u+1)} (X : α → (Profinite.{u}ᵒᵖ ⥤ Type (u+1))) (T) :
  (∏ X).obj T ≅ ∏ (λ i, (X i).obj T) :=
preserves_limit_iso ((evaluation _ _).obj T) _ ≪≫
has_limit.iso_of_nat_iso (discrete.nat_iso $ λ p, iso.refl _)

@[simp, reassoc]
lemma functor_prod_eval_iso_spec
  {α : Type (u+1)} (X : α → (Profinite.{u}ᵒᵖ ⥤ Type (u+1))) (T) (i : α) :
  (functor_prod_eval_iso X T).hom ≫ pi.π _ i =
  (pi.π X i : ∏ X ⟶ X i).app _ :=
begin
  dsimp [functor_prod_eval_iso],
  simp only [category.assoc],
  erw limit.lift_π,
  dsimp,
  erw limit.lift_π_assoc,
  erw category.comp_id,
  refl,
end

@[simp, reassoc]
lemma functor_prod_eval_iso_spec'
  {α : Type (u+1)} (X : α → (Profinite.{u}ᵒᵖ ⥤ Type (u+1))) (T) (i : α) :
  (functor_prod_eval_iso X T).inv ≫ (pi.π X i : ∏ X ⟶ X i).app _ =
  pi.π _ i :=
by { rw iso.inv_comp_eq, rw functor_prod_eval_iso_spec }

def filtration_pow_iso_aux (j : ℕ) (r : ℝ≥0) :
  (ProFiltPseuNormGrp₁.level.obj r).obj
    (∏ λ i : ulift.{u} (fin j), (PFPNGT₁_to_PFPNG₁ₑₗ _).obj M) ≅
  (∏ λ i : ulift.{u} (fin j), pseudo_normed_group.filtration_obj M r) :=
preserves_limit_iso (ProFiltPseuNormGrp₁.level.obj r) _ ≪≫
has_limit.iso_of_nat_iso (discrete.nat_iso $ λ q, iso.refl _)

@[simp, reassoc]
lemma filtration_pow_iso_aux_spec (j : ℕ) (r : ℝ≥0) (i) :
  (filtration_pow_iso_aux M j r).hom ≫ pi.π
    (λ i : ulift.{u} (fin j), pseudo_normed_group.filtration_obj M r) i =
  (ProFiltPseuNormGrp₁.level.obj r).map (pi.π _ i) :=
begin
  dsimp [filtration_pow_iso_aux],
  simp only [category.assoc],
  erw limit.lift_π,
  dsimp,
  erw limit.lift_π_assoc,
  erw category.comp_id,
  refl,
end

@[simp, reassoc]
lemma filtration_pow_iso_aux_spec' (j : ℕ) (r : ℝ≥0) (i) :
  (filtration_pow_iso_aux M j r).inv ≫
  (ProFiltPseuNormGrp₁.level.obj r).map (pi.π _ i) =
  pi.π _ i :=
by { rw iso.inv_comp_eq, rw filtration_pow_iso_aux_spec }

def ProFiltPseuNormGrp₁.product_fan {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrp₁.{u}) :
  fan X :=
fan.mk (ProFiltPseuNormGrp₁.product X) $ λ i, ProFiltPseuNormGrp₁.product.π _ _

def ProFiltPseuNormGrp₁.is_limit_product_fan {α : Type u} [fintype α]
  (X : α → ProFiltPseuNormGrp₁.{u}) :
  is_limit (ProFiltPseuNormGrp₁.product_fan X) :=
{ lift := λ S, ProFiltPseuNormGrp₁.product.lift _ _ $ λ i, S.π.app ⟨i⟩,
  fac' := begin
    rintro S ⟨j⟩,
    dsimp,
    erw ProFiltPseuNormGrp₁.product.lift_π,
  end,
  uniq' := begin
    intros S m hm,
    apply ProFiltPseuNormGrp₁.product.hom_ext,
    rintro j,
    erw hm ⟨j⟩,
    erw ProFiltPseuNormGrp₁.product.lift_π,
  end }

def ProFiltPseuNormGrp₁.product_pow_iso {α : Type u} [fintype α]
  (X : α → ProFiltPseuNormGrp₁.{u}) :
  ∏ X ≅ ProFiltPseuNormGrp₁.product X :=
(limit.is_limit _).cone_point_unique_up_to_iso (ProFiltPseuNormGrp₁.is_limit_product_fan _)

@[simp, reassoc]
lemma ProFiltPseuNormGrp₁.product_pow_iso_spec {α : Type u} [fintype α]
  (X : α → ProFiltPseuNormGrp₁.{u}) (i) :
  (ProFiltPseuNormGrp₁.product_pow_iso X).hom ≫
  ProFiltPseuNormGrp₁.product.π _ _ = pi.π _ i :=
begin
  erw ProFiltPseuNormGrp₁.product.lift_π,
  refl,
end

@[simp, reassoc]
lemma ProFiltPseuNormGrp₁.product_pow_iso_spec' {α : Type u} [fintype α]
  (X : α → ProFiltPseuNormGrp₁.{u}) (i) :
  (ProFiltPseuNormGrp₁.product_pow_iso X).inv ≫ pi.π _ i =
  ProFiltPseuNormGrp₁.product.π _ _ :=
by { rw iso.inv_comp_eq, rw ProFiltPseuNormGrp₁.product_pow_iso_spec }

def filtration_pow_proj (j : ℕ) (r : ℝ≥0) (i : fin j) :
  pseudo_normed_group.filtration_obj.{u} (↥M ^ j) r ⟶
  pseudo_normed_group.filtration_obj.{u} M r :=
{ to_fun := λ t, ⟨t.1 i, t.2 _⟩,
  continuous_to_fun := begin
    let e := (comphaus_filtered_pseudo_normed_group.filtration_pi_homeo
      (λ i : (fin j), M) r),
    let t := _, change continuous t,
    suffices : continuous (t ∘ e.symm), by simpa using this,
    convert continuous_apply i,
    ext, refl,
  end }

def filtration_pow_iso_aux'₀ (j : ℕ) (r : ℝ≥0) :
  pseudo_normed_group.filtration_obj.{u} (↥M ^ j) r ≅
  (ProFiltPseuNormGrp₁.level.{u}.obj r).obj
  (ProFiltPseuNormGrp₁.product.{u} (λ (i : ulift.{u 0} (fin j)),
    (PFPNGT₁_to_PFPNG₁ₑₗ.{u} r').obj M)) :=
-- This can't be the best way to do this, but at this point I'm quite annoyed.
{ hom :=
  { to_fun := λ q, ⟨λ i, q.1 i.down, begin
      intros i,
      apply q.2,
    end⟩,
    continuous_to_fun := begin
      rw (comphaus_filtered_pseudo_normed_group.filtration_pi_homeo
        (λ i : ulift.{u} (fin j), M) r).inducing.continuous_iff,
      apply continuous_pi,
      intros i, dsimp,
      let e := (comphaus_filtered_pseudo_normed_group.filtration_pi_homeo
        (λ i : (fin j), M) r),
      let t := _, change continuous t,
      suffices : continuous (t ∘ e.symm), by simpa using this,
      convert continuous_apply i.down,
      ext, refl,
    end },
  inv :=
  { to_fun := λ q, ⟨λ i, q.1 ⟨i⟩, begin
      intros i,
      apply q.2,
    end⟩,
    continuous_to_fun := begin
      let e₁ := (comphaus_filtered_pseudo_normed_group.filtration_pi_homeo
        (λ i : (fin j), M) r),
      let e₂ := (comphaus_filtered_pseudo_normed_group.filtration_pi_homeo
        (λ i : ulift.{u} (fin j), M) r),
      let t := _, change continuous t,
      suffices : continuous (e₁ ∘ t ∘ e₂.symm), by simpa using this,
      apply continuous_pi,
      intros i, convert continuous_apply (ulift.up i),
      ext, refl,
    end },
  hom_inv_id' := by { ext, refl },
  inv_hom_id' := by { ext _ ⟨⟩, refl } }

@[simp, reassoc]
lemma filtration_pow_iso_aux'₀_spec (j : ℕ) (r : ℝ≥0) (i) :
  (filtration_pow_iso_aux'₀ M j r).hom ≫
  ((ProFiltPseuNormGrp₁.level.obj r).map $ ProFiltPseuNormGrp₁.product.π _ i) =
  filtration_pow_proj M j r i.down := by { ext, refl }

@[simp, reassoc]
lemma filtration_pow_iso_aux'₀_spec' (j : ℕ) (r : ℝ≥0) (i : ulift.{u} (fin j)) :
  (filtration_pow_iso_aux'₀ M j r).inv ≫ filtration_pow_proj M j r i.down =
  ((ProFiltPseuNormGrp₁.level.obj r).map $ ProFiltPseuNormGrp₁.product.π _ i) :=
by { cases i, ext _ ⟨k⟩, refl }

def filtration_pow_iso_aux' (j : ℕ) (r : ℝ≥0) :
  pseudo_normed_group.filtration_obj.{u} (↥M ^ j) r ≅
  (ProFiltPseuNormGrp₁.level.obj r).obj
    (∏ λ i : ulift.{u} (fin j), (PFPNGT₁_to_PFPNG₁ₑₗ _).obj M) :=
filtration_pow_iso_aux'₀ _ _ _ ≪≫
(ProFiltPseuNormGrp₁.level.obj r).map_iso (ProFiltPseuNormGrp₁.product_pow_iso _).symm

@[simp, reassoc]
lemma filtration_pow_iso_aux'_spec (j : ℕ) (r : ℝ≥0) (i) :
  (filtration_pow_iso_aux' M j r).hom ≫
  (ProFiltPseuNormGrp₁.level.obj r).map (pi.π _ i) =
  filtration_pow_proj _ _ _ i.down :=
begin
  dsimp [filtration_pow_iso_aux'],
  simp only [category.assoc],
  simp only [← functor.map_comp, ProFiltPseuNormGrp₁.product_pow_iso_spec'],
  simp,
end

@[simp, reassoc]
lemma filtration_pow_iso_aux'_spec' (j : ℕ) (r : ℝ≥0) (i : ulift.{u} (fin j)) :
  (filtration_pow_iso_aux' M j r).inv ≫ filtration_pow_proj _ _ _ i.down =
  (ProFiltPseuNormGrp₁.level.obj r).map (pi.π _ i) :=
by { rw iso.inv_comp_eq, rw filtration_pow_iso_aux'_spec }

def filtration_pow_iso (j : ℕ) (r : ℝ≥0) :
  pseudo_normed_group.filtration_obj.{u} (M ^ j) r ≅
  ∏ λ i : ulift.{u} (fin j), pseudo_normed_group.filtration_obj M r :=
filtration_pow_iso_aux' _ _ _ ≪≫ filtration_pow_iso_aux _ _ _

@[simp, reassoc]
lemma filtration_pow_iso_spec (j : ℕ) (r : ℝ≥0) (i : ulift.{u} (fin j)) :
  (filtration_pow_iso M j r).hom ≫ pi.π _ i =
  filtration_pow_proj _ _ _ i.down :=
begin
  dsimp [filtration_pow_iso],
  simp,
end

@[simp, reassoc]
lemma filtration_pow_iso_spec' (j : ℕ) (r : ℝ≥0) (i : ulift.{u} (fin j)) :
  (filtration_pow_iso M j r).inv ≫ filtration_pow_proj _ _ _ i.down =
  pi.π _ i :=
by { rw iso.inv_comp_eq, rw filtration_pow_iso_spec }

def profinite_pow_filtration_iso_component (j : ℕ) (r : ℝ≥0) (T : Profinite.{u}) :
  ulift.{u+1} (T ⟶ pseudo_normed_group.filtration_obj.{u} (↥M ^ j) r) ≅
  ∏ λ (i : ulift.{u+1} (fin j)), ulift.{u+1}
    (T ⟶ (ProFiltPseuNormGrp₁.level.{u}.obj r).obj ((PFPNGT₁_to_PFPNG₁ₑₗ.{u} r').obj M)) :=
ulift_functor.map_iso
((yoneda.flip.obj (op T)).map_iso $ filtration_pow_iso _ _ _) ≪≫
{ hom := pi.lift $ λ i f, ulift.up $ ulift.down f ≫ pi.π _ (ulift.up i.down),
  inv := λ t, ulift.up $ pi.lift $ λ i,
    let q := pi.π (λ (i : ulift.{u+1 0} (fin j)),
      ulift.{u+1 u}
      (T ⟶ (ProFiltPseuNormGrp₁.level.{u}.obj r).obj
      ((PFPNGT₁_to_PFPNG₁ₑₗ.{u} r').obj M))) (ulift.up $ ulift.down i) t in q.down,
  hom_inv_id' := begin
    ext ⟨t⟩ : 2, dsimp,
    apply limit.hom_ext, rintros ⟨⟨q⟩⟩,
    simp,
  end,
  inv_hom_id' := begin
    apply limit.hom_ext, rintro ⟨⟨q⟩⟩,
    simp only [category.assoc, limit.lift_π, fan.mk_π_app, category.id_comp],
    ext t,
    dsimp,
    rw [← comp_apply, limit.lift_π],
    refl,
  end }

.

@[simp, reassoc]
lemma profinite_pow_filtration_iso_component_spec (j : ℕ) (r : ℝ≥0) (T : Profinite.{u})
  (i : ulift.{u+1} (fin j)) :
  (profinite_pow_filtration_iso_component M j r T).hom ≫ pi.π _ i =
  ulift_functor.map ((yoneda.flip.obj (op T)).map $ filtration_pow_proj _ _ _ i.down) :=
begin
  dsimp [profinite_pow_filtration_iso_component],
  simp,
  ext ⟨t⟩ : 2,
  dsimp,
  simp,
end

@[simp, reassoc]
lemma profinite_pow_filtration_iso_component_spec' (j : ℕ) (r : ℝ≥0) (T : Profinite.{u})
  (i : ulift.{u+1} (fin j)) :
  (profinite_pow_filtration_iso_component M j r T).inv ≫
  ulift_functor.map ((yoneda.flip.obj (op T)).map $ filtration_pow_proj _ _ _ i.down) =
  pi.π _ i :=
by { rw iso.inv_comp_eq, rw profinite_pow_filtration_iso_component_spec }

def profinite_pow_filtration_iso (j : ℕ) (r : ℝ≥0) :
  (pseudo_normed_group.filtration_obj.{u} (↥M ^ j) r).to_Condensed ≅
  ∏ λ (k : ulift.{u+1 0} (fin j)), ((ProFiltPseuNormGrp₁.level.obj r).obj
    ((PFPNGT₁_to_PFPNG₁ₑₗ _).obj M)).to_Condensed :=
begin
  refine Sheaf.iso.mk _ _ _,
  refine _ ≪≫ (Condensed_prod_val_iso _).symm,
  refine nat_iso.of_components _ _,
  { intros T,
    refine _ ≪≫ (functor_prod_eval_iso _ _).symm,
    refine profinite_pow_filtration_iso_component _ _ _ _ },
  { intros X Y f, dsimp,
    apply (is_limit_of_preserves ((evaluation _ _).obj Y) (limit.is_limit _)).hom_ext,
    rintro ⟨i⟩, swap, apply_instance,
    dsimp, simp only [category.assoc],
    erw [functor_prod_eval_iso_spec', nat_trans.naturality,
      functor_prod_eval_iso_spec'_assoc, profinite_pow_filtration_iso_component_spec,
      profinite_pow_filtration_iso_component_spec_assoc],
    ext, refl }
end

@[simp, reassoc]
lemma profinite_pow_filtration_iso_spec (j : ℕ) (r : ℝ≥0) (i : ulift.{u+1} (fin j)) :
  (profinite_pow_filtration_iso M j r).hom ≫ pi.π _ i =
  Profinite_to_Condensed.map (filtration_pow_proj _ _ _ i.down) :=
begin
  dsimp [profinite_pow_filtration_iso, Sheaf.iso.mk],
  ext1, dsimp,
  simp only [category.assoc],
  rw Condensed_prod_val_iso_spec',
  ext T : 2,
  dsimp,
  simp only [category.assoc],
  rw functor_prod_eval_iso_spec',
  erw profinite_pow_filtration_iso_component_spec,
  refl,
end

@[simp, reassoc]
lemma profinite_pow_filtration_iso_spec' (j : ℕ) (r : ℝ≥0) (i : ulift.{u+1} (fin j)) :
  (profinite_pow_filtration_iso M j r).inv ≫
  Profinite_to_Condensed.map (filtration_pow_proj _ _ _ i.down) = pi.π _ i :=
by { rw iso.inv_comp_eq, rw profinite_pow_filtration_iso_spec }

def combine (hι : monotone ι) (n : ℕ) : ℕ →o ℝ≥0 :=
{ to_fun := λ t, κ (ι $ ulift.up t) n,
  monotone' := begin
    intros a b h,
    apply (fact.out (monotone (function.swap κ n))),
    apply hι,
    exact h
  end }

def iso_on_the_left_zero₀ :
 (∐ λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X 0 ≅
 (∐ λ (k : ulift.{u+1 0} ℕ), ((QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X 0) :=
begin
  refine preserves_colimit_iso (homological_complex.eval _ _ 0) _ ≪≫ _,
  refine has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ i, iso.refl _),
end

@[simp, reassoc]
lemma iso_on_the_left_zero₀_spec' (i : ulift.{u+1} ℕ) :
  sigma.ι (λ (k : ulift.{u+1 0} ℕ), ((QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X 0) i ≫
  (iso_on_the_left_zero₀ BD κ M ι).inv =
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) i).f 0 :=
begin
  dsimp [iso_on_the_left_zero₀],
  erw colimit.ι_desc_assoc, dsimp, simp only [category.id_comp],
  erw colimit.ι_desc, refl,
end

@[simp, reassoc]
lemma iso_on_the_left_zero₀_spec (i : ulift.{u+1} ℕ) :
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) i).f 0 ≫
  (iso_on_the_left_zero₀ BD κ M ι).hom =
  sigma.ι (λ (k : ulift.{u+1 0} ℕ), ((QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X 0) i :=
by { rw ← iso.eq_comp_inv, rw iso_on_the_left_zero₀_spec', }

def iso_on_the_left_zero  :
 (∐ λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X 0 ≅
  ∐ λ (i : as_small.{u+1 0 0} ℕ), CondensedSet_to_Condensed_Ab.{u}.obj
      (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X 0))),
      (Condensed.as_nat_diagram.{u} M.to_CHFPNG (combine.{u} κ ι hι 0)).obj i) :=
begin
  refine iso_on_the_left_zero₀ BD κ M _ ≪≫ _,
  refine sigma.map_iso _,
  rintros ⟨j⟩,
  dsimp [QprimeFP_int, QprimeFP_nat, FreeAb.eval, functor.map_FreeAb,
    FPsystem, FPsystem.X],
  refine CondensedSet_to_Condensed_Ab.map_iso _,
  refine profinite_pow_filtration_iso M (BD.data.X 0) (κ (ι ⟨j⟩) 0), --≪≫ _,
end

@[simp, reassoc]
lemma iso_on_the_left_zero_spec' (k : ℕ) :
  sigma.ι (λ (i : as_small.{u+1 0 0} ℕ), CondensedSet_to_Condensed_Ab.{u}.obj
    (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X 0))),
    (Condensed.as_nat_diagram.{u} M.to_CHFPNG (combine.{u} κ ι hι 0)).obj i))
    ⟨k⟩ ≫ (iso_on_the_left_zero _ _ _ _ _).inv =
  CondensedSet_to_Condensed_Ab.map (profinite_pow_filtration_iso M
    (BD.data.X 0) (κ (ι ⟨k⟩) 0)).inv ≫
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f 0 :=
begin
  dsimp [iso_on_the_left_zero],
  erw colimit.ι_desc_assoc, dsimp,
  rw [category.assoc],
  slice_lhs 2 3
  { rw iso_on_the_left_zero₀_spec' },
end

@[simp, reassoc]
lemma iso_on_the_left_zero_spec (k : ℕ) :
  CondensedSet_to_Condensed_Ab.map (profinite_pow_filtration_iso M
    (BD.data.X 0) (κ (ι ⟨k⟩) 0)).inv ≫
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f 0 ≫
  (iso_on_the_left_zero _ _ _ _ _).hom =
  sigma.ι (λ (i : as_small.{u+1 0 0} ℕ), CondensedSet_to_Condensed_Ab.{u}.obj
    (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X 0))),
    (Condensed.as_nat_diagram.{u} M.to_CHFPNG (combine.{u} κ ι hι 0)).obj i))
    ⟨k⟩ :=
begin
  rw [← category.assoc, ← iso.eq_comp_inv, iso_on_the_left_zero_spec'],
end

@[simp, reassoc]
lemma iso_on_the_left_zero_spec_alt (k : ℕ) :
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f 0 ≫
  (iso_on_the_left_zero _ _ _ _ _).hom =
  CondensedSet_to_Condensed_Ab.map (profinite_pow_filtration_iso M
    (BD.data.X 0) (κ (ι ⟨k⟩) 0)).hom ≫
  sigma.ι (λ (i : as_small.{u+1 0 0} ℕ), CondensedSet_to_Condensed_Ab.{u}.obj
    (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X 0))),
    (Condensed.as_nat_diagram.{u} M.to_CHFPNG (combine.{u} κ ι hι 0)).obj i))
    ⟨k⟩ :=
begin
  rw [← functor.map_iso_hom, ← iso.inv_comp_eq,
    functor.map_iso_inv, iso_on_the_left_zero_spec],
end

def pseudo_normed_group.map_filtration (M : Type*) [profinitely_filtered_pseudo_normed_group M]
  (a b : ℝ≥0) (h : a ≤ b) :
  pseudo_normed_group.filtration_obj M a ⟶ pseudo_normed_group.filtration_obj M b :=
{ to_fun := pseudo_normed_group.cast_le' h,
  continuous_to_fun := begin
    haveI : fact (a ≤ b) := ⟨h⟩,
    apply comphaus_filtered_pseudo_normed_group.continuous_cast_le,
  end }

lemma pow_filtration_hom_ext {T : Profinite.{u}} (j : ℕ) (r : ℝ≥0)
  (f g : T ⟶ pseudo_normed_group.filtration_obj (M^j) r)
  (h : ∀ k, f ≫ filtration_pow_proj M j r k = g ≫ filtration_pow_proj M j r k) : f = g :=
begin
  ext t x,
  specialize h x,
  apply_fun (λ e, (e t).1) at h,
  exact h,
end

lemma iso_on_the_left_zero_conj_aux (j : ℕ) :
  ((profinite_pow_filtration_iso.{u} M (BD.data.X 0) (κ (ι {down := j}) 0)).hom ≫
    (Condensed.as_nat_diagram_pow.{u} M.to_CHFPNG (combine.{u} κ ι hι 0) (BD.data.X 0)).map
    (as_small.up.{0 0 u+1}.map (hom_of_le.{0} (nat.le_succ _)))) ≫
  (profinite_pow_filtration_iso.{u} M (BD.data.X 0) (κ (ι {down := j + 1}) 0)).inv =
  Profinite_to_Condensed.map (pseudo_normed_group.map_filtration _ _ _
    (fact.out (monotone (function.swap κ 0)) (hι $ by { exact_mod_cast j.le_succ }))) :=
begin
  rw iso.comp_inv_eq,
  apply limit.hom_ext, rintro ⟨k⟩,
  dsimp [Condensed.as_nat_diagram_pow, pow_functor], simp only [category.assoc],
  erw profinite_pow_filtration_iso_spec,
  simp only [lim_map_π, discrete.nat_trans_app],
  erw profinite_pow_filtration_iso_spec_assoc,
  dsimp [Condensed.as_nat_diagram, restrict_diagram,
    CompHausFiltPseuNormGrp.level_Condensed_diagram,
    CompHausFiltPseuNormGrp.level_Condensed_diagram'],
  rw ← Profinite_to_Condensed.map_comp,
  have h : κ (ι ⟨j⟩) 0 ≤ κ (ι ⟨j+1⟩) 0,
  { apply fact.out (monotone (function.swap κ 0)),
    apply hι,
    exact_mod_cast j.le_succ },
  change _ ≫ Profinite_to_Condensed.map (pseudo_normed_group.map_filtration M _ _ h) = _,
  rw ← Profinite_to_Condensed.map_comp,
  congr' 1,
end

lemma iso_on_the_left_zero_conj :
  ((QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD.data κ M)).f 0) =
  (iso_on_the_left_zero _ _ _ _ hι).hom ≫
  (Condensed.coproduct_to_coproduct (Condensed.as_nat_diagram_pow M.to_CHFPNG
    (combine κ ι hι 0) _ ⋙ _) - 𝟙 _) ≫ (iso_on_the_left_zero _ _ _ _ hι).inv :=
begin
  dsimp [QprimeFP.shift_sub_id],
  simp only [comp_sub, sub_comp, category.id_comp, iso.hom_inv_id,
    category.assoc], congr' 1,
  apply (is_colimit_of_preserves (homological_complex.eval _ _ _)
    (colimit.is_colimit _)).hom_ext, swap, apply_instance,
  rintros ⟨⟨j⟩⟩, dsimp,
  erw [← homological_complex.comp_f, colimit.ι_desc],
  dsimp [sigma_shift_cone],
  rw iso_on_the_left_zero_spec_alt_assoc,
  erw colimit.ι_desc_assoc, dsimp,
  simp only [category.assoc],
  slice_rhs 3 4
  { erw iso_on_the_left_zero_spec' },
  simp only [← category.assoc],
  congr' 1,
  dsimp [CondensedSet_to_Condensed_Ab],
  simp only [← functor.map_comp],
  dsimp [QprimeFP_int, QprimeFP_nat, FreeAb.eval, functor.map_FreeAb,
    FPsystem, FPsystem.X, FreeAb.of_functor],
  rw free_abelian_group.lift.of, dsimp,
  congr' 1,
  ext S : 2,
  dsimp,
  simp only [← functor.map_comp], congr' 1,
  simp only [← nat_trans.comp_app, ← Sheaf.hom.comp_val],
  rw iso_on_the_left_zero_conj_aux,
  ext, refl,
end

def iso_on_the_left_neg₀ (q : ℕ) :
 (∐ λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X (-[1+q]) ≅
 (∐ λ (k : ulift.{u+1 0} ℕ), ((QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X (-[1+q])) :=
begin
  refine preserves_colimit_iso (homological_complex.eval _ _ _) _ ≪≫ _,
  refine has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ i, iso.refl _),
end

@[simp, reassoc]
lemma iso_on_the_left_neg₀_spec' (q : ℕ) (i : ulift.{u+1} ℕ) :
  sigma.ι (λ (k : ulift.{u+1 0} ℕ), ((QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X (-[1+q])) i ≫
  (iso_on_the_left_neg₀ BD κ M ι q).inv =
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) i).f (-[1+q]) :=
begin
  dsimp [iso_on_the_left_neg₀],
  erw colimit.ι_desc_assoc, dsimp, simp only [category.id_comp],
  erw colimit.ι_desc, refl,
end

@[simp, reassoc]
lemma iso_on_the_left_neg₀_spec (q : ℕ) (i : ulift.{u+1} ℕ) :
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) i).f (-[1+q]) ≫
  (iso_on_the_left_neg₀ BD κ M ι q).hom =
  sigma.ι (λ (k : ulift.{u+1 0} ℕ), ((QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X (-[1+q])) i :=
by { rw ← iso.eq_comp_inv, rw iso_on_the_left_neg₀_spec', }

def iso_on_the_left_neg (q : ℕ) :
 (∐ λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)).X (-[1+q]) ≅
  ∐ λ (i : as_small.{u+1 0 0} ℕ), CondensedSet_to_Condensed_Ab.{u}.obj
      (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X (q+1)))),
      (Condensed.as_nat_diagram.{u} M.to_CHFPNG (combine.{u} κ ι hι (q+1))).obj i) :=
begin
  refine iso_on_the_left_neg₀ BD κ M _ q ≪≫ _,
  refine sigma.map_iso _,
  rintros ⟨j⟩,
  dsimp [QprimeFP_int, QprimeFP_nat, FreeAb.eval, functor.map_FreeAb,
    FPsystem, FPsystem.X],
  refine CondensedSet_to_Condensed_Ab.map_iso _,
  refine profinite_pow_filtration_iso M (BD.data.X (q+1)) (κ (ι ⟨j⟩) (q+1)),
end

@[simp, reassoc]
lemma iso_on_the_left_neg_spec' (q : ℕ) (k : ℕ) :
  sigma.ι (λ (i : as_small.{u+1 0 0} ℕ), CondensedSet_to_Condensed_Ab.{u}.obj
    (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X (q+1)))),
    (Condensed.as_nat_diagram.{u} M.to_CHFPNG (combine.{u} κ ι hι (q+1))).obj i))
    ⟨k⟩ ≫ (iso_on_the_left_neg _ _ _ _ _ q).inv =
  CondensedSet_to_Condensed_Ab.map (profinite_pow_filtration_iso M
    (BD.data.X (q+1)) (κ (ι ⟨k⟩) (q+1))).inv ≫
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f (-[1+q]) :=
begin
  dsimp [iso_on_the_left_neg],
  erw colimit.ι_desc_assoc, dsimp,
  rw [category.assoc],
  slice_lhs 2 3
  { rw iso_on_the_left_neg₀_spec' },
end

@[simp, reassoc]
lemma iso_on_the_left_neg_spec (q : ℕ) (k : ℕ) :
  CondensedSet_to_Condensed_Ab.map (profinite_pow_filtration_iso M
    (BD.data.X (q+1)) (κ (ι ⟨k⟩) (q+1))).inv ≫
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f (-[1+q]) ≫
  (iso_on_the_left_neg _ _ _ _ _ q).hom =
  sigma.ι (λ (i : as_small.{u+1 0 0} ℕ), CondensedSet_to_Condensed_Ab.{u}.obj
    (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X (q+1)))),
    (Condensed.as_nat_diagram.{u} M.to_CHFPNG (combine.{u} κ ι hι (q+1))).obj i))
    ⟨k⟩ :=
begin
  rw [← category.assoc, ← iso.eq_comp_inv, iso_on_the_left_neg_spec'],
end

@[simp, reassoc]
lemma iso_on_the_left_neg_spec_alt (q : ℕ) (k : ℕ) :
  (sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f (-[1+q]) ≫
  (iso_on_the_left_neg _ _ _ _ _ q).hom =
  CondensedSet_to_Condensed_Ab.map (profinite_pow_filtration_iso M
    (BD.data.X (q+1)) (κ (ι ⟨k⟩) (q+1))).hom ≫
  sigma.ι (λ (i : as_small.{u+1 0 0} ℕ), CondensedSet_to_Condensed_Ab.{u}.obj
    (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X (q+1)))),
    (Condensed.as_nat_diagram.{u} M.to_CHFPNG (combine.{u} κ ι hι (q+1))).obj i))
    ⟨k⟩ :=
begin
  rw [← functor.map_iso_hom, ← iso.inv_comp_eq,
    functor.map_iso_inv, iso_on_the_left_neg_spec],
end

lemma iso_on_the_left_neg_conj_aux (q : ℕ) (j : ℕ) :
  ((profinite_pow_filtration_iso.{u} M (BD.data.X (q+1)) (κ (ι {down := j}) (q+1))).hom ≫
    (Condensed.as_nat_diagram_pow.{u} M.to_CHFPNG (combine.{u} κ ι hι (q+1)) (BD.data.X (q+1))).map
    (as_small.up.{0 0 u+1}.map (hom_of_le.{0} (nat.le_succ _)))) ≫
  (profinite_pow_filtration_iso.{u} M (BD.data.X (q+1)) (κ (ι {down := j + 1}) (q+1))).inv =
  Profinite_to_Condensed.map (pseudo_normed_group.map_filtration _ _ _
    (fact.out (monotone (function.swap κ (q+1))) (hι $ by { exact_mod_cast j.le_succ }))) :=
begin
  rw iso.comp_inv_eq,
  apply limit.hom_ext, rintro ⟨k⟩,
  dsimp [Condensed.as_nat_diagram_pow, pow_functor], simp only [category.assoc],
  erw profinite_pow_filtration_iso_spec,
  simp only [lim_map_π, discrete.nat_trans_app],
  erw profinite_pow_filtration_iso_spec_assoc,
  dsimp [Condensed.as_nat_diagram, restrict_diagram,
    CompHausFiltPseuNormGrp.level_Condensed_diagram,
    CompHausFiltPseuNormGrp.level_Condensed_diagram'],
  rw ← Profinite_to_Condensed.map_comp,
  have h : κ (ι ⟨j⟩) (q+1) ≤ κ (ι ⟨j+1⟩) (q+1),
  { apply fact.out (monotone (function.swap κ (q+1))),
    apply hι,
    exact_mod_cast j.le_succ },
  change _ ≫ Profinite_to_Condensed.map (pseudo_normed_group.map_filtration M _ _ h) = _,
  rw ← Profinite_to_Condensed.map_comp,
  congr' 1,
end

lemma iso_on_the_left_neg_conj (q : ℕ) :
  ((QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD.data κ M)).f (-[1+q])) =
  (iso_on_the_left_neg _ _ _ _ hι _).hom ≫
  (Condensed.coproduct_to_coproduct (Condensed.as_nat_diagram_pow M.to_CHFPNG
    (combine κ ι hι (q+1)) _ ⋙ _) - 𝟙 _) ≫ (iso_on_the_left_neg _ _ _ _ hι _).inv :=
begin
  dsimp [QprimeFP.shift_sub_id],
  simp only [comp_sub, sub_comp, category.id_comp, iso.hom_inv_id,
    category.assoc], congr' 1,
  apply (is_colimit_of_preserves (homological_complex.eval _ _ _)
    (colimit.is_colimit _)).hom_ext, swap, apply_instance,
  rintros ⟨⟨j⟩⟩, dsimp,
  erw [← homological_complex.comp_f, colimit.ι_desc],
  dsimp [sigma_shift_cone],
  rw iso_on_the_left_neg_spec_alt_assoc,
  erw colimit.ι_desc_assoc, dsimp,
  simp only [category.assoc],
  slice_rhs 3 4
  { erw iso_on_the_left_neg_spec' },
  simp only [← category.assoc],
  congr' 1,
  dsimp [CondensedSet_to_Condensed_Ab],
  simp only [← functor.map_comp],
  dsimp [QprimeFP_int, QprimeFP_nat, FreeAb.eval, functor.map_FreeAb,
    FPsystem, FPsystem.X, FreeAb.of_functor],
  rw free_abelian_group.lift.of, dsimp,
  congr' 1,
  ext S : 2,
  dsimp,
  simp only [← functor.map_comp], congr' 1,
  simp only [← nat_trans.comp_app, ← Sheaf.hom.comp_val],
  rw iso_on_the_left_neg_conj_aux,
  ext, refl,
end

.

def product_iso_biproduct {A : Type (u+2)} [category.{u+1} A]
  [abelian A] {α : Type (u+1)} [fintype α] (X : α → A) :
  ∏ X ≅ biproduct X :=
(limit.is_limit _).cone_point_unique_up_to_iso (biproduct.is_limit _)

@[simp, reassoc]
lemma product_iso_biproduct_spec' {A : Type (u+2)} [category.{u+1} A]
  [abelian A] {α : Type (u+1)} [fintype α] (X : α → A) (t) :
  (product_iso_biproduct X).inv ≫ pi.π _ t =
  biproduct.π _ t :=
begin
  erw limit.lift_π, refl,
end

@[simp, reassoc]
lemma product_iso_biproduct_spec {A : Type (u+2)} [category.{u+1} A]
  [abelian A] {α : Type (u+1)} [fintype α] (X : α → A) (t) :
  (product_iso_biproduct X).hom ≫ biproduct.π _ t = pi.π _ t :=
begin
  rw [← iso.eq_inv_comp, product_iso_biproduct_spec'],
end

def Condensed_product_iso_biproduct (q : ℕ) :
  Condensed_Ab_to_CondensedSet.{u}.obj
  (∏ λ (i : ulift.{u+1 0} (fin (q))), M.to_Condensed) ≅
  Condensed_Ab_to_CondensedSet.{u}.obj
  (⨁ λ (i : ulift.{u+1 0} (fin (q))), M.to_Condensed) :=
Condensed_Ab_to_CondensedSet.map_iso $
(limit.is_limit _).cone_point_unique_up_to_iso (biproduct.is_limit _)

@[simp, reassoc]
lemma Condensed_product_iso_biproduct_spec' (q : ℕ) (i : ulift.{u+1} (fin q)) :
  (Condensed_product_iso_biproduct M q).inv ≫
  Condensed_Ab_to_CondensedSet.map (pi.π _ i) =
  Condensed_Ab_to_CondensedSet.map (biproduct.π _ i) :=
begin
  dsimp only [Condensed_product_iso_biproduct, functor.map_iso_inv, functor.map_iso_hom],
  rw ← Condensed_Ab_to_CondensedSet.map_comp,
  erw limit.lift_π,
  refl,
end

@[simp, reassoc]
lemma Condensed_product_iso_biproduct_spec (q : ℕ) (i : ulift.{u+1} (fin q)) :
  (Condensed_product_iso_biproduct M q).hom ≫
  Condensed_Ab_to_CondensedSet.map (biproduct.π _ i) =
  Condensed_Ab_to_CondensedSet.map (pi.π _ i) :=
begin
  rw ← iso.eq_inv_comp, rw Condensed_product_iso_biproduct_spec',
end

def Condensed_product_iso_product (q : ℕ) :
  Condensed_Ab_to_CondensedSet.{u}.obj
  (∏ λ (i : ulift.{u+1 0} (fin (q))), M.to_Condensed) ≅
  ∏ λ i : ulift.{u+1} (fin q), Condensed_Ab_to_CondensedSet.obj M.to_Condensed :=
preserves_limit_iso Condensed_Ab_to_CondensedSet _ ≪≫
has_limit.iso_of_nat_iso (discrete.nat_iso $ λ i, iso.refl _)

@[simp, reassoc]
lemma Condensed_product_iso_product_spec (q : ℕ) (i : ulift.{u+1} (fin q)) :
  (Condensed_product_iso_product M q).hom ≫ pi.π _ i =
  Condensed_Ab_to_CondensedSet.map (pi.π _ i) :=
begin
  dsimp [Condensed_product_iso_product], simp only [category.assoc],
  erw limit.lift_π,
  dsimp,
  erw [category.comp_id, limit.lift_π], refl,
end

@[simp, reassoc]
lemma Condensed_product_iso_product_spec' (q : ℕ) (i : ulift.{u+1} (fin q)) :
  (Condensed_product_iso_product M q).inv ≫ Condensed_Ab_to_CondensedSet.map (pi.π _ i) =
  pi.π _ i :=
by { rw iso.inv_comp_eq, rw Condensed_product_iso_product_spec }

def iso_on_the_right_zero :
  CondensedSet_to_Condensed_Ab.{u}.obj
  (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X 0))),
  (Condensed.as_nat_cocone.{u} M.to_CHFPNG (combine.{u} κ ι hι 0)).X) ≅
  ((BD.eval' freeCond'.{u}).obj M.to_Condensed).X 0 :=
begin
  refine CondensedSet_to_Condensed_Ab.map_iso _,
  dsimp,
  refine _ ≪≫ Condensed_product_iso_biproduct _ _,
  refine (Condensed_product_iso_product _ _).symm,
end

-- Why is this thing tagged with simp in the first place!?
local attribute [-simp] forget_map_eq_coe

@[simp, reassoc]
lemma iso_on_the_right_zero_spec' (i : ulift.{u+1} (fin (BD.data.X 0))) :
  (iso_on_the_right_zero BD κ M ι hι).inv ≫
  CondensedSet_to_Condensed_Ab.map (pi.π _ i) =
  CondensedSet_to_Condensed_Ab.map (Condensed_Ab_to_CondensedSet.map $ biproduct.π _ i) :=
begin
  dsimp [iso_on_the_right_zero], simp only [← functor.map_comp], congr' 1, ext S : 2,
  dsimp, simp_rw [← functor.map_comp, ← nat_trans.comp_app, ← Sheaf.hom.comp_val, category.assoc],
  erw Condensed_product_iso_product_spec,
  erw Condensed_product_iso_biproduct_spec',
  refl,
end

@[simp, reassoc]
lemma iso_on_the_right_zero_spec (i : ulift.{u+1} (fin (BD.data.X 0))) :
  (iso_on_the_right_zero BD κ M ι hι).hom ≫
  CondensedSet_to_Condensed_Ab.map (Condensed_Ab_to_CondensedSet.map $ biproduct.π _ i) =
  CondensedSet_to_Condensed_Ab.map (pi.π _ i) :=
by { rw ← iso.eq_inv_comp, rw iso_on_the_right_zero_spec' }

lemma iso_on_the_right_zero_conj :
  ((QprimeFP_sigma_proj BD κ M ι).f 0) =
  (iso_on_the_left_zero _ _ _ _ hι).hom ≫
  Condensed.coproduct_presentation_with_pow CondensedSet_to_Condensed_Ab M.to_CHFPNG
    (combine _ _ _ _) _ ≫ (iso_on_the_right_zero _ _ _ _ _).hom :=
begin
  dsimp [QprimeFP_sigma_proj],
  apply (is_colimit_of_preserves (homological_complex.eval _ _ 0)
    (colimit.is_colimit (discrete.functor $
    λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)))).hom_ext,
  rintros ⟨⟨i⟩⟩, dsimp, rw [← homological_complex.comp_f, colimit.ι_desc], dsimp,
  slice_rhs 1 2 { erw iso_on_the_left_zero_spec_alt BD κ M ι hι i },
  dsimp [Condensed.coproduct_presentation_with_pow,
    -CondensedSet_to_Condensed_Ab_map], simp only [category.assoc, colimit.ι_desc],
  dsimp [-CondensedSet_to_Condensed_Ab_map],
  dsimp [QprimeFP_incl, -CondensedSet_to_Condensed_Ab_map, iso_on_the_right_zero],
  simp only [← functor.map_comp], congr' 1,
  simp_rw ← category.assoc, rw [← iso.comp_inv_eq, iso.eq_comp_inv],
  apply limit.hom_ext, rintro ⟨j⟩,
  simp only [category.assoc, lim_map_π],
  erw Condensed_product_iso_product_spec,
  erw Condensed_product_iso_biproduct_spec',
  erw profinite_pow_filtration_iso_spec_assoc,
  ext S : 3,
  dsimp [QprimeFP_incl_aux],
  rw [← whisker_right_app, ← nat_trans.comp_app],
  have := (is_limit_of_preserves.{u+1 u+1 u+1 u+1 u+2 u+2}
    (Condensed_Ab_to_CondensedSet.{u} ⋙ CondensedSet_to_presheaf.{u})
    (biproduct.is_limit.{u+1 u+2} (λ (i : ulift.{u+1 0} (fin (BD.data.X 0))),
    M.to_Condensed))).fac,
  dsimp at this, erw this _ ⟨j⟩,
  ext, refl,
end

.

def iso_on_the_right_neg (q : ℕ) :
  CondensedSet_to_Condensed_Ab.{u}.obj
  (∏ λ (j : ulift.{u+1 0} (fin (BD.data.X (q+1)))),
  (Condensed.as_nat_cocone.{u} M.to_CHFPNG (combine.{u} κ ι hι (q+1))).X) ≅
  ((BD.eval' freeCond'.{u}).obj M.to_Condensed).X (-[1+q]) :=
begin
  refine CondensedSet_to_Condensed_Ab.map_iso _,
  dsimp,
  refine _ ≪≫ Condensed_product_iso_biproduct _ _,
  refine (Condensed_product_iso_product _ _).symm,
end

@[simp, reassoc]
lemma iso_on_the_right_neg_spec' (q : ℕ) (i : ulift.{u+1} (fin (BD.data.X (q+1)))) :
  (iso_on_the_right_neg BD κ M ι hι q).inv ≫
  CondensedSet_to_Condensed_Ab.map (pi.π _ i) =
  CondensedSet_to_Condensed_Ab.map (Condensed_Ab_to_CondensedSet.map $ biproduct.π _ i) :=
begin
  dsimp [iso_on_the_right_neg], simp only [← functor.map_comp], congr' 1, ext S : 2,
  dsimp, simp_rw [← functor.map_comp, ← nat_trans.comp_app, ← Sheaf.hom.comp_val, category.assoc],
  erw Condensed_product_iso_product_spec,
  erw Condensed_product_iso_biproduct_spec',
  refl,
end

@[simp, reassoc]
lemma iso_on_the_right_neg_spec (q : ℕ) (i : ulift.{u+1} (fin (BD.data.X (q+1)))) :
  (iso_on_the_right_neg BD κ M ι hι q).hom ≫
  CondensedSet_to_Condensed_Ab.map (Condensed_Ab_to_CondensedSet.map $ biproduct.π _ i) =
  CondensedSet_to_Condensed_Ab.map (pi.π _ i) :=
by { rw ← iso.eq_inv_comp, rw iso_on_the_right_neg_spec' }

lemma iso_on_the_right_neg_conj (q : ℕ) :
  ((QprimeFP_sigma_proj BD κ M ι).f (-[1+q])) =
  (iso_on_the_left_neg _ _ _ _ hι q).hom ≫
  Condensed.coproduct_presentation_with_pow CondensedSet_to_Condensed_Ab M.to_CHFPNG
    (combine _ _ _ _) _ ≫ (iso_on_the_right_neg _ _ _ _ _ _).hom :=
begin
  dsimp [QprimeFP_sigma_proj],
  apply (is_colimit_of_preserves (homological_complex.eval _ _ (-[1+q]))
    (colimit.is_colimit (discrete.functor $
    λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj (ι k)))).hom_ext,
  rintros ⟨⟨i⟩⟩, dsimp, rw [← homological_complex.comp_f, colimit.ι_desc], dsimp,
  slice_rhs 1 2 { erw iso_on_the_left_neg_spec_alt BD κ M ι hι q i },
  dsimp [Condensed.coproduct_presentation_with_pow,
    -CondensedSet_to_Condensed_Ab_map], simp only [category.assoc, colimit.ι_desc],
  dsimp [-CondensedSet_to_Condensed_Ab_map],
  dsimp [QprimeFP_incl, -CondensedSet_to_Condensed_Ab_map, iso_on_the_right_neg],
  simp only [← functor.map_comp], congr' 1,
  simp_rw ← category.assoc, rw [← iso.comp_inv_eq, iso.eq_comp_inv],
  apply limit.hom_ext, rintro ⟨j⟩,
  simp only [category.assoc, lim_map_π],
  erw Condensed_product_iso_product_spec,
  erw Condensed_product_iso_biproduct_spec',
  erw profinite_pow_filtration_iso_spec_assoc,
  ext S : 3,
  dsimp [QprimeFP_incl_aux],
  rw [← whisker_right_app, ← nat_trans.comp_app],
  erw (is_limit_of_preserves.{u+1 u+1 u+1 u+1 u+2 u+2} (Condensed_Ab_to_CondensedSet.{u} ⋙
    CondensedSet_to_presheaf.{u})
    (biproduct.is_limit.{u+1 u+2} (λ (i : ulift.{u+1 0} (fin (BD.data.X (q+1)))),
    M.to_Condensed))).fac _ ⟨j⟩,
  ext, refl,
end

end ses_setup

lemma QprimeFP.mono (n : ℤ) :
  mono ((QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD.data κ M)).f n) :=
begin
  rcases n with (_|q)|q,
  { erw iso_on_the_left_zero_conj,
    apply_with mono_comp { instances := ff }, apply_instance,
    apply_with mono_comp { instances := ff }, swap, apply_instance,
    apply Condensed.mono_coproduct_to_coproduct },
  { apply mono_of_is_zero_object,
    let e :
      (∐ λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj
        (ι k)).X (int.of_nat q.succ) ≅
      ∐ λ k : ulift.{u+1} ℕ, ((QprimeFP_int.{u} r' BD.data κ M).obj
        (ι k)).X (int.of_nat q.succ) :=
      preserves_colimit_iso (homological_complex.eval _ _ _) _ ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ p, iso.refl _),
    apply is_zero_of_iso_of_zero _ e.symm,
    apply is_zero_colimit, intros j,
    exact is_zero_zero _ },
  { erw iso_on_the_left_neg_conj,
    apply_with mono_comp { instances := ff }, apply_instance,
    apply_with mono_comp { instances := ff }, swap, apply_instance,
    apply Condensed.mono_coproduct_to_coproduct },

  /-
  rw Condensed.mono_iff_ExtrDisc, intros T,
  let Q := QprimeFP_int r' BD.data κ M,
  let e : ((∐ λ (k : ulift.{u+1 0} ℕ), Q.obj (ι k)).X n).val.obj
    (op T.val) ≅ _ := coproduct_eval_iso _ _ _,
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
  -/
end
.

lemma QprimeFP_sigma_proj_eq_0 (n : ℕ) : ((QprimeFP_sigma_proj BD κ M ι).f (n+1:ℤ)) = 0 :=
by { apply is_zero.eq_of_tgt, apply is_zero_zero }

-- move me
lemma AddCommGroup.eq_of_is_zero (A : AddCommGroup) (hA : is_zero A) (x y : A) : x = y :=
begin
  rw [← Ab.pt_apply' x, ← Ab.pt_apply' y], congr' 1, apply hA.eq_of_tgt,
end

attribute [simps] Condensed_Ab_to_presheaf

lemma QprimeFP.epi (hι : monotone ι)
  (hκι : ∀ (r : ℝ≥0) q, ∃ (n : ℕ), r ≤ (combine.{u} κ ι hι q) n)
  (n : ℤ) : epi ((QprimeFP_sigma_proj BD κ M ι).f n) :=
begin
  rcases n with (_|q)|q,
  { erw iso_on_the_right_zero_conj,
    swap, assumption,
    apply_with epi_comp { instances := ff }, apply_instance,
    apply_with epi_comp { instances := ff }, swap, apply_instance,
    rw Condensed.coproduct_presentation_with_pow_eq,
    apply_with epi_comp { instances := ff }, swap, apply_instance,
    swap, { intros r, apply hκι },
    exact Condensed.epi_coproduct_to_colimit (Condensed.as_nat_diagram_pow.{u} M.to_CHFPNG
      (combine.{u} κ ι hι 0) (BD.data.X 0) ⋙ CondensedSet_to_Condensed_Ab.{u}) },
  { apply epi_of_is_zero,
    exact is_zero_zero _ },
  { erw iso_on_the_right_neg_conj, swap, assumption,
    apply_with epi_comp { instances := ff }, apply_instance,
    apply_with epi_comp { instances := ff }, swap, apply_instance,
    rw Condensed.coproduct_presentation_with_pow_eq,
    apply_with epi_comp { instances := ff }, swap, apply_instance,
    swap, { intros r, apply hκι },
    exact Condensed.epi_coproduct_to_colimit (Condensed.as_nat_diagram_pow.{u} M.to_CHFPNG
      (combine.{u} κ ι hι (q + 1)) (BD.data.X (q + 1)) ⋙ CondensedSet_to_Condensed_Ab.{u}) }

  /-
  rw is_epi_iff_forall_surjective,
  intros S,
  rcases n with ((_|n)|n),
  swap,
  { intro f,
    refine ⟨0, _⟩, apply AddCommGroup.eq_of_is_zero,
    rw [← evaluation_obj_obj, ← Condensed_Ab_to_presheaf_obj],
    apply functor.map_is_zero, apply functor.map_is_zero, exact is_zero_zero _, },
  { admit },
  { admit },
  -/
end

lemma QprimeFP.exact (n : ℤ)
  (hκι : ∀ (r : ℝ≥0) q, ∃ (n : ℕ), r ≤ (combine.{u} κ ι hι q) n) :
  exact
    ((QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD.data κ M)).f n)
    ((QprimeFP_sigma_proj BD κ M ι).f n) :=
begin
  rcases n with (_|q)|q,
  { erw iso_on_the_left_zero_conj,
    erw iso_on_the_right_zero_conj, swap, assumption,
    rw ← category.assoc,
    apply category_theory.exact_comp_inv_hom_comp,
    rw exact_iso_comp, rw exact_comp_iso,
    apply (Condensed.short_exact_sequence_with_pow _ _ _ _ _).exact,
    intros r, apply hκι },
  { apply exact_of_is_zero,
    let e :
      (∐ λ (k : ulift.{u+1 0} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj
        (ι k)).X (int.of_nat q.succ) ≅
      ∐ λ k : ulift.{u+1} ℕ, ((QprimeFP_int.{u} r' BD.data κ M).obj
        (ι k)).X (int.of_nat q.succ) :=
      preserves_colimit_iso (homological_complex.eval _ _ _) _ ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ p, iso.refl _),
    apply is_zero_of_iso_of_zero _ e.symm,
    apply is_zero_colimit, intros j,
    exact is_zero_zero _ },
  { erw iso_on_the_left_neg_conj,
    erw iso_on_the_right_neg_conj, swap, assumption,
    rw ← category.assoc,
    apply category_theory.exact_comp_inv_hom_comp,
    rw exact_iso_comp, rw exact_comp_iso,
    apply (Condensed.short_exact_sequence_with_pow _ _ _ _ _).exact,
    intros r, apply hκι },
end

lemma QprimeFP.short_exact
  (hκι : ∀ (r : ℝ≥0) q, ∃ (n : ℕ), r ≤ (combine.{u} κ ι hι q) n) (n : ℤ) :
  short_exact
    ((QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD.data κ M)).f n)
    ((QprimeFP_sigma_proj BD κ M ι).f n) :=
begin
  apply_with short_exact.mk {instances:=ff},
  { apply QprimeFP.mono },
  { apply QprimeFP.epi, assumption, },
  { apply QprimeFP.exact, assumption },
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
  apply colimit.hom_ext, rintro ⟨j⟩,
  dsimp [sigma_shift, sigma_shift', sigma_shift_cone, sigma_map],
  rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc],
  dsimp [sigma_shift_cone],
  simp only [category.assoc, colimit.ι_desc],
  dsimp [sigma_shift_cone],
  --  refl,
  -- simp only [sigma_shift, sigma_shift', sigma_shift_cone, sigma_map, colimit.ι_desc_assoc,
  --   colimit.ι_desc, cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc,
  --   discrete.nat_trans_app],
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
  apply colimit.hom_ext, rintro ⟨j⟩,
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
  apply colimit.hom_ext, rintro ⟨j⟩,
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
  dsimp only [FreeAb.eval, functor.map_FreeAb, FPsystem.Tinv, FP2.Tinv_app, FreeAb.of_functor],
  simp only [free_abelian_group.lift_map, function.comp, function.comp.left_id],
  rw [free_abelian_group.lift.of],
  simp only [← functor.map_comp],
  congr' 1,
  ext1,
  let x := biproduct.is_limit (λ (i : ulift (fin (BD.data.X n))), M.to_Condensed),
  let y := is_limit_of_preserves (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf) x,
  apply y.hom_ext, rintro ⟨k⟩,
  simp only [Sheaf.hom.comp_val, category.assoc, QprimeFP_incl_aux, y.fac],
  rw [← CondensedSet_to_presheaf_map, ← functor.comp_map],
  simp only [functor.map_cone_π_app, bicone.to_cone_π_app, biproduct.bicone_π],
  rw [← functor.map_comp, biproduct.map_π, functor.map_comp],
  have : ((Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map_cone
    (biproduct.bicone (λ (i : ulift (fin (BD.data.X n))), M.to_Condensed)).to_cone).π.app ⟨k⟩ =
    (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf).map
    (biproduct.π (λ (j : ulift (fin (BD.data.X n))), M.to_Condensed) k) := rfl,
  rw [← this, ← category.assoc, y.fac], clear this y x,
  ext S : 2,
  dsimp only [nat_trans.comp_app, QprimeFP_incl_aux', functor.comp_map,
    Condensed_Ab_to_CondensedSet_map, CondensedSet_to_presheaf_map,
    Profinite_to_Condensed_map_val, whisker_right_app, ProFiltPseuNormGrpWithTinv₁.Tinv_cond,
    forget_map_eq_coe, yoneda_map_app, CompHausFiltPseuNormGrp.to_Condensed_map,
    Ab.ulift_map_apply],
  simp only [← ulift_functor.map_comp],
  refl
end

lemma commsq_sigma_proj_ι [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ κ c n)] :
  commsq (QprimeFP_sigma_proj BD κ₂ M ι) (sigma_map (λ (k : ulift ℕ), ι k)
    (QprimeFP_int.ι BD.data κ₂ κ M)) (𝟙 _) (QprimeFP_sigma_proj BD κ M ι) :=
commsq.of_eq begin
  simp only [category.comp_id],
  apply colimit.hom_ext, intro j,
  simp only [QprimeFP_sigma_proj, sigma_map, colimit.ι_desc_assoc, colimit.ι_desc,
    cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc],
  dsimp only [QprimeFP_incl, QprimeFP_int.ι, whisker_right_app,
    package.eval', functor.comp_map],
  rw [← functor.map_comp],
  refine congr_arg _ _,
  ext n : 2,
  dsimp only [homological_complex.comp_f, data.eval_functor, functor.comp_obj, functor.flip_obj_map,
    homological_complex.functor_eval_map_app_f, data.eval_functor'_obj_X_map, functor.comp_map,
    QprimeFP_nat.ι, whisker_right_app, functor.map_homological_complex_map_f],
  rw [map_FreeAb_comp_map],
  dsimp only [FreeAb.eval, functor.map_FreeAb, FPsystem.res, FP2.res_app, FreeAb.of_functor],
  simp only [free_abelian_group.lift_map, function.comp, function.comp.left_id],
  rw [free_abelian_group.lift.of, ← functor.map_comp],
  refine congr_arg _ _,
  ext1,
  let x := biproduct.is_limit (λ (i : ulift (fin (BD.data.X n))), M.to_Condensed),
  let y := is_limit_of_preserves (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf) x,
  apply y.hom_ext, intro k,
  simp only [Sheaf.hom.comp_val, category.assoc, QprimeFP_incl_aux, y.fac],
  rw [← CondensedSet_to_presheaf_map, ← functor.comp_map],
  ext S : 2,
  dsimp only [nat_trans.comp_app, QprimeFP_incl_aux', functor.comp_map,
    Condensed_Ab_to_CondensedSet_map, CondensedSet_to_presheaf_map,
    Profinite_to_Condensed_map_val, whisker_right_app,
    forget_map_eq_coe, yoneda_map_app, CompHausFiltPseuNormGrp.to_Condensed_map,
    Ab.ulift_map_apply],
  simp only [← ulift_functor.map_comp],
  refl,
end

end step6
