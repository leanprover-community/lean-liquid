import thm95.polyhedral_iso
import pseudo_normed_group.homotopy
import rescale.FiltrationPow

/-!
# A complex canonically isomorphic to `row 1` of the double complex

We have
```
lemma double_complex.row_one :
  (double_complex BD κ r r' V Λ M N).row 1 =
  BD.system κ r V r' (Hom ((cosimplicial Λ N).obj (mk 0)) M) := rfl
```

We want to "rewrite" this row in such a way that it is the target
of the homotopies that will be constructed formally from `BD.homotopy`.

Concretely, we want:
```
(((data.mul N).obj BD.data).system (rescale_constants κ N) r V r').obj (op (Hom Λ M)) ≅
  (thm95.double_complex BD.data κ r r' V Λ M N).row 1
```

This means that we need to multiply `BD` by `N`,
and then take the system associated with `rescale N (Hom Λ M)`.

We need the following isomorphisms

* `BD.system M^N = (BD.mul N).system M`
* `Hom (rescale N (Λ^N)) M = (rescale N (Hom Λ M)^N` (2 steps?)
* `(cosimplicial Λ N).obj (mk 0) = rescale N (Λ^N)`

-/

universe variables u

noncomputable theory

open_locale nnreal big_operators kronecker

local attribute [instance] type_pow

local attribute [reducible] CLCFPTinv₂ CLCFPTinv₂.res
  breen_deligne.universal_map.eval_CLCFPTinv₂

-- move this
namespace category_theory

namespace arrow

variables {C : Type*} [category C] {X Y Z X' Y' Z' : C}
variables (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')

lemma mk_comp_congr (hf : arrow.mk f = arrow.mk f') (hg : arrow.mk g = arrow.mk g') :
  arrow.mk (f ≫ g) = arrow.mk (f' ≫ g') :=
by { cases hf, cases hg, refl }

end arrow

end category_theory

open category_theory

section rescale

variables {BD : breen_deligne.data}
variables (κ : ℕ → ℝ≥0)
variables [BD.suitable κ]
variables (r : ℝ≥0) (V : SemiNormedGroup.{u}) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0)
variables (M : ProFiltPseuNormGrpWithTinv.{u} r')

-- move this
instance rescale_constants_suitable (N : ℝ≥0) :
  BD.suitable (rescale_constants κ N) :=
by { delta rescale_constants, apply_instance }

variables (BD)

open breen_deligne opposite ProFiltPseuNormGrpWithTinv (of)

section

def FiltrationPow_rescale_iso (n : ℕ) (N : ℝ≥0) :
  ((Filtration r').obj c).obj ((ProFiltPseuNormGrpWithTinv.Pow r' n).obj (of r' (rescale N M))) ≅
    ((Filtration r').obj (c * N⁻¹)).obj ((ProFiltPseuNormGrpWithTinv.Pow r' n).obj M) :=
iso.refl _

def complex_rescale_iso (N : ℝ≥0) :
  (BD.complex (rescale_constants κ N) r V r' c).obj (op M) ≅
  (BD.complex κ r V r' c).obj (op $ of r' $ rescale N M) :=
homological_complex.hom.iso_of_components
begin
  intro i,
  refine CLCTinv.map_iso r V _ _ _ _ _ _ _ _,
  { refine (FiltrationPow_rescale_iso _ _ _ _ ≪≫
      Filtration_cast_eq r' _ _ (mul_assoc c (κ i) (N⁻¹)) _).op, },
  { refine (FiltrationPow_rescale_iso _ _ _ _ ≪≫
      Filtration_cast_eq _ (r' * (c * κ i) * N⁻¹) (r' * (c * (κ i * N⁻¹)))
      (by simp only [mul_assoc]) _).op, },
  { refl },
  { refl }
end
begin
  intros i j hij,
  apply arrow.mk_injective,
  dsimp only [data.complex_obj_d, universal_map.eval_CLCFPTinv, universal_map.eval_CLCFPTinv₂,
    _root_.id, SemiNormedGroup.equalizer.map_nat_app, CLCTinv.map_iso_hom, CLCTinv.map, unop_op,
    Filtration_cast_eq, iso.op_hom],
  simp only [SemiNormedGroup.equalizer.map_comp_map, universal_map.eval_CLCFP_rescale,
    ← CLCFP.res_def', nat_iso.app_hom, functor.map_iso_hom, Filtration_map_app,
    FiltrationPow_rescale_iso, iso.refl_trans],
  apply SemiNormedGroup.equalizer.map_congr,
  { have := @universal_map.res_comp_eval_CLCFP V r'
      (c * (κ i * N⁻¹)) (c * κ i * N⁻¹) (c * (κ j * N⁻¹)) (c * κ j * N⁻¹)
      (BD.X j) (BD.X i) (BD.d j i) ⟨(mul_assoc _ _ _).le⟩ _ _ ⟨(mul_assoc _ _ _).le⟩,
    replace := nat_trans.congr_app this.symm (op M),
    replace := congr_arg arrow.mk this,
    refine (this.trans _).symm,
    apply arrow.mk_comp_congr, { refl }, { rw universal_map.eval_CLCFP_rescale } },
  { have := @universal_map.res_comp_eval_CLCFP V r'
      (r' * (c * (κ i * N⁻¹))) (r' * (c * κ i) * N⁻¹) (r' * (c * (κ j * N⁻¹))) (r' * (c * κ j) * N⁻¹)
      (BD.X j) (BD.X i) (BD.d j i) ⟨le_of_eq $ by simp only [mul_assoc]⟩ _ _ ⟨le_of_eq $ by simp only [mul_assoc]⟩,
    replace := nat_trans.congr_app this.symm (op M),
    replace := congr_arg arrow.mk this,
    refine (this.trans _).symm,
    apply arrow.mk_comp_congr, { refl }, { rw universal_map.eval_CLCFP_rescale } },
  any_goals { refl },
end
.

noncomputable
def system_rescale_iso (N : ℝ≥0) :
  (BD.system (rescale_constants κ N) r V r').obj (op M) ≅
  (BD.system κ r V r').obj (op $ of r' $ rescale N M) :=
nat_iso.of_components (λ c, complex_rescale_iso BD κ r V c.unop _ _)
begin
  intros c₁ c₂ h,
  ext i : 2,
  apply arrow.mk_injective,
  erw [homological_complex.comp_f, homological_complex.comp_f],
  dsimp only [data.system_obj, CLCFPTinv₂.res, complex_rescale_iso,
    homological_complex.hom.iso_of_components, CLCTinv.map_iso_hom, CLCTinv.map_nat_app],
  simp only [CLCTinv.map_comp_map],
  refl,
end

end

end rescale

namespace thm95

open breen_deligne polyhedral_lattice opposite

variables (BD : breen_deligne.data) (κ : ℕ → ℝ≥0) [BD.suitable κ]
variables (r : ℝ≥0) (V : SemiNormedGroup.{u}) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)] (c : ℝ≥0)

section

variables {m n : ℕ} (ϕ : universal_map m n) (g : basic_universal_map m n)
variables (c₁ c₂ : ℝ≥0) (N : ℕ) [fact (0 < N)]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r')

lemma eval_FP_mul [g.suitable c₂ c₁] :
  (CLC V).map (FiltrationPow.mul_iso.{u u} r' c₁ M N n).hom.op ≫
    (CLC V).map ((basic_universal_map.eval_FP r' c₂ c₁ g).app (ProFiltPseuNormGrpWithTinv.of r' (M ^ N))).op =
  (CLC V).map ((basic_universal_map.eval_FP r' c₂ c₁ ((basic_universal_map.mul N) g)).app M).op ≫
    (CLC V).map (FiltrationPow.mul_iso.{u u} r' c₂ M N m).hom.op :=
begin
  simp only [← (CLC V).map_comp, ← op_comp], congr' 2,
  rw [← iso.inv_comp_eq, ← category.assoc, ← iso.eq_comp_inv],
  exact basic_universal_map.mul_iso_eval_FP r' c₁ c₂ g N M
end

lemma eval_CLCFP_mul [ϕ.suitable c₂ c₁] {_ : (universal_map.mul N ϕ).suitable c₂ c₁} :
  (((universal_map.mul N ϕ).eval_CLCFP V r' c₁ c₂).app (op M) ≫
    (CLC V).map (FiltrationPow.mul_iso.{u u} r' c₂ M N m).op.hom) =
  ((CLC V).map (FiltrationPow.mul_iso.{u u} r' c₁ M N n).op.hom ≫
   ((ϕ.eval_CLCFP V r' c₁ c₂).app (op (ProFiltPseuNormGrpWithTinv.of r' (M ^ N))) : _)) :=
begin
  dsimp only [universal_map.eval_CLCFP, whisker_right_app],
  simp only [universal_map.eval_LCFP_eq_eval_LCFP', universal_map.eval_LCFP',
    ← nat_trans.app_hom_apply, ← functor.map_add_hom_apply,
    add_monoid_hom.map_sum, add_monoid_hom.map_gsmul],
  rw [preadditive.sum_comp, preadditive.comp_sum],
  symmetry, have hN : 0 < N := fact.out _,
  apply finset.sum_bij (λ g hg, basic_universal_map.mul N g),
  { intros g hg, rw universal_map.mem_support_mul N hN, refine ⟨g, hg, rfl⟩ },
  { intros g hg,
    simp only [preadditive.comp_gsmul, preadditive.gsmul_comp, universal_map.coeff_mul N hN],
    congr' 1,
    have : g.suitable c₂ c₁ := universal_map.suitable_of_mem_support _ _ _ _ hg, resetI,
    rw [← basic_universal_map.eval_LCFP_eq_eval_LCFP' _ _ _ _ g this,
        ← basic_universal_map.eval_LCFP_eq_eval_LCFP'],
    swap, { apply basic_universal_map.mul_suitable },
    dsimp only [basic_universal_map.eval_LCFP, nat_trans.app_hom_apply, functor.map_add_hom_apply,
      whisker_right_app, nat_trans.op_app, unop_op],
    simp only [← functor.comp_map],
    apply eval_FP_mul },
  { intros g₁ g₂ hg₁ hg₂ H, exact basic_universal_map.mul_injective N hN H },
  { intro g, rw universal_map.mem_support_mul N hN, rintro ⟨g', h1, h2⟩, exact ⟨g', h1, h2⟩ }
end

def mul_complex_iso (c : ℝ≥0) :
  (((data.mul N).obj BD).complex κ r V r' c).obj (op M) ≅
  (BD.complex κ r V r' c).obj (op (ProFiltPseuNormGrpWithTinv.of r' $ M^N)) :=
homological_complex.hom.iso_of_components
begin
  intro i,
  refine CLCTinv.map_iso r V _ _ _ _ _ _ _ _,
  { exact (FiltrationPow.mul_iso.{u u} r' (c * κ i) M N (BD.X i)).op },
  { exact (FiltrationPow.mul_iso.{u u} r' (r' * (c * κ i)) M N (BD.X i)).op },
  { refl },
  { refl }
end
begin
  intros i j hij,
  apply arrow.mk_injective,
  dsimp only [data.complex_obj_d, universal_map.eval_CLCFPTinv, universal_map.eval_CLCFPTinv₂,
    _root_.id, SemiNormedGroup.equalizer.map_nat_app, CLCTinv.map_iso_hom, CLCTinv.map,
    data.mul_obj_d],
  simp only [SemiNormedGroup.equalizer.map_comp_map],
  apply SemiNormedGroup.equalizer.map_congr,
  { rw eval_CLCFP_mul },
  { rw eval_CLCFP_mul },
  all_goals { refl }
end

end

def mul_system_iso (N : ℕ) [fact (0 < N)] (M : ProFiltPseuNormGrpWithTinv.{u} r') :
  (((data.mul N).obj BD).system κ r V r').obj (op M) ≅
  (BD.system κ r V r').obj (op (ProFiltPseuNormGrpWithTinv.of r' $ M^N)) :=
nat_iso.of_components (λ c, mul_complex_iso BD κ r V N M c.unop)
begin
  intros c₁ c₂ hc,
  ext i : 2,
  apply arrow.mk_injective,
  erw [homological_complex.comp_f, homological_complex.comp_f],
  dsimp only [data.system_obj, CLCFPTinv₂.res, mul_complex_iso,
    homological_complex.hom.iso_of_components, CLCTinv.map_iso_hom, CLCTinv.map_nat_app],
  simp only [CLCTinv.map_comp_map],
  refl,
end

def mul_rescale_iso_row_one
  (N : ℕ) [fact (0 < N)] (N' : ℝ≥0) (h : N' = N)
  (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r') :
  (((data.mul N).obj BD).system (rescale_constants κ N') r V r').obj (op (Hom Λ M)) ≅
    ((thm95.double_complex BD κ r r' V Λ M N).row 1) :=
(mul_system_iso _ _ r V N _) ≪≫
(system_rescale_iso _ κ r V _ _) ≪≫
((BD.system κ r V r').map_iso $
  (PolyhedralLattice.Hom_cosimplicial_zero_iso Λ N r' M N' h).op)

lemma mul_rescale_iso_row_one_strict
  (N : ℕ) [fact (0 < N)] (N' : ℝ≥0) (h : N' = N)
  (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r')
  (c : ℝ≥0) (i : ℕ)
  (x : (((data.mul N).obj BD).system (rescale_constants κ N') r V r').obj (op (Hom Λ M)) c i) :
  ∥(mul_rescale_iso_row_one BD κ r V N N' h Λ M).hom x∥ = ∥x∥ :=
begin
  apply normed_group_hom.norm_eq_of_isometry,
  refine isometry.comp (isometry.comp _ _) _,
  { apply data.system_map_iso_isometry, },
  { dsimp only, apply CLCTinv.map_iso_isometry, },
  { apply CLCTinv.map_iso_isometry, },
end
.

lemma quux (N : ℕ) [fact (0 < N)] (M : ProFiltPseuNormGrpWithTinv.{u} r') (c₁ c₂ : ℝ≥0) (i : ℕ)
  [(universal_map.sum i N).suitable c₂ c₁] {_ : ((finset.univ : finset (fin N)).sum (basic_universal_map.proj i)).suitable c₂ c₁} :
  (universal_map.eval_CLCFP V r' c₁ c₂ (universal_map.sum i N)).app (op M) =
  (CLC V).map ((basic_universal_map.eval_FP r' c₂ c₁ ((finset.univ : finset (fin N)).sum (basic_universal_map.proj i))).app M).op :=
by { dsimp only [universal_map.sum], rw [universal_map.eval_CLCFP_of], refl }

lemma bar (N : ℕ) [fact (0 < N)] (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r')
  (c₁ c₂ : ℝ≥0) (hc : c₁ * N⁻¹ = c₂) (n : ℕ)
  {_ : ((finset.univ : finset (fin N)).sum (basic_universal_map.proj n)).suitable c₂ c₁} :
  (FiltrationPow_rescale_iso c₁ (ProFiltPseuNormGrpWithTinv.of r' ((Hom Λ M) ^ N)) n N ≪≫
     ((Filtration r').map_iso (eq_to_iso hc)).app
       ((ProFiltPseuNormGrpWithTinv.Pow r' n).obj (ProFiltPseuNormGrpWithTinv.of r' ((Hom Λ M) ^ N)))).inv ≫
  ((Filtration r').obj c₁).map ((ProFiltPseuNormGrpWithTinv.Pow r' n).map (Λ.Hom_sum N r' M)) =
  (FiltrationPow.mul_iso.{u u} r' c₂ (Hom.{u u} Λ M) N n).hom ≫
    (basic_universal_map.eval_FP.{u} r' c₂ c₁ (finset.univ.sum (basic_universal_map.proj n))).app (Hom.{u u} Λ M) :=
begin
  dsimp only [FiltrationPow_rescale_iso], rw [iso.refl_trans],
  dsimp only [FiltrationPow.mul_iso_hom, nat_iso.app_inv, functor.map_iso_inv,
    Pow_obj, ProFiltPseuNormGrpWithTinv.coe_of, Filtration_map_app],
  ext x i : 3,
  erw [comp_apply, comp_apply],
  dsimp only [Filtration_obj_map_to_fun, Pow_Pow_X_hom_to_fun, continuous_map.coe_mk,
    profinitely_filtered_pseudo_normed_group_with_Tinv_hom.level_coe, subtype.coe_mk,
    Filtration.cast_le_to_fun, pseudo_normed_group.coe_cast_le,
    basic_universal_map.eval_FP, basic_universal_map.eval_png₀,
    ProFiltPseuNormGrpWithTinv.Pow_map,
    profinitely_filtered_pseudo_normed_group_with_Tinv.pi_map_to_fun],
  rw [← profinitely_filtered_pseudo_normed_group_hom.coe_to_add_monoid_hom,
    ← profinitely_filtered_pseudo_normed_group_hom.to_add_monoid_hom_hom_apply],
  simp only [PolyhedralLattice.Hom_sum_apply, add_monoid_hom.map_sum,
    add_monoid_hom.finset_sum_apply, finset.sum_apply],
  apply fintype.sum_congr,
  intro j,
  simp only [profinitely_filtered_pseudo_normed_group_hom.coe_to_add_monoid_hom,
    profinitely_filtered_pseudo_normed_group_hom.to_add_monoid_hom_hom_apply,
    basic_universal_map.eval_png_apply, ProFiltPseuNormGrpWithTinv.Pow_Pow_X_hom_to_fun,
    ProFiltPseuNormGrpWithTinv.Pow_Pow_X_equiv_symm_apply,
    equiv.inv_fun_as_coe, equiv.symm_symm, equiv.trans_apply, equiv.symm_trans_apply,
    equiv.arrow_congr_apply, function.comp, equiv.refl_apply, equiv.curry_symm_apply,
    function.uncurry, equiv.prod_comm_symm, equiv.prod_comm_apply, prod.fst_swap, prod.snd_swap],
  rw [← fin_prod_fin_equiv.sum_comp], swap, { apply_instance },
  simp only [basic_universal_map.proj,
    matrix.reindex_linear_equiv_apply, matrix.reindex_apply, matrix.minor_apply,
    equiv.punit_prod_symm_apply, matrix.kronecker, matrix.one_apply,
    basic_universal_map.proj_aux, equiv.symm_apply_apply,
    boole_mul, ← ite_and, @eq_comm _ i],
  sorry,
  -- simp only [← prod.mk.inj_iff, ite_smul, one_smul, zero_smul, prod.mk.eta],
  -- convert (finset.sum_ite_eq' finset.univ (j, i) (λ p, x.val p.2 p.1)).symm using 2,
  -- { simp only [finset.mem_univ, if_true, subtype.val_eq_coe], },
  -- { ext ⟨a, b⟩,
  --   split_ifs; refl }
end

lemma foo (N : ℕ) [fact (0 < N)] (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r')
  (c₁ c₂ : ℝ≥0) (hc : c₁ * N⁻¹ = c₂) (i : ℕ) [H : universal_map.suitable c₂ c₁ (universal_map.sum i N)] :
  (CLC V).map ((FiltrationPow r' c₁ i).op.map (Λ.Hom_sum N r' M).op) ≫
    (CLC V).map (FiltrationPow_rescale_iso c₁ ((ProFiltPseuNormGrpWithTinv.of r' ((Hom Λ M) ^ N))) i N ≪≫
      Filtration_cast_eq r' (c₁ * N⁻¹) c₂ hc ((ProFiltPseuNormGrpWithTinv.Pow r' i).obj ((ProFiltPseuNormGrpWithTinv.of r' ((Hom Λ M) ^ N))))).op.inv =
  ((universal_map.eval_CLCFP V r' c₁ c₂ (universal_map.sum i N)).app (op (Hom Λ M)) ≫ (CLC V).map (FiltrationPow.mul_iso.{u u} r' c₂ (Hom Λ M) N i).op.hom) :=
begin
  rw [← (CLC V).map_comp],
  dsimp only [FiltrationPow, category_theory.functor.op_map, category_theory.functor.comp_map,
    Filtration_cast_eq, quiver.hom.unop_op],
  rw [iso.op_inv, quux, ← (CLC V).map_comp, iso.op_hom, ← op_comp, ← op_comp],
  swap, { exact @basic_universal_map.suitable_of_suitable_of _ _ _ _ _ H },
  congr' 2,
  apply bar,
end

lemma row_map_eq_sum_comp
  (N : ℕ) [fact (0 < N)] (N' : ℝ≥0) (h : N' = N)
  [∀ (i : ℕ), universal_map.suitable (rescale_constants κ N' i) (κ i) ((BD.sum N).f i)]
  (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r') :
  (thm95.double_complex BD κ r r' V Λ M N).row_map 0 1 =
    (iso.refl ((BD.system κ r V r').obj (op (Hom Λ M)))).inv ≫
    (BD_system_map (BD.sum N) κ
      (rescale_constants κ N') r V).app (op (Hom Λ M)) ≫
    (thm95.mul_rescale_iso_row_one BD κ r V N N' h Λ M).hom :=
begin
  unfreezingI { subst h },
  dsimp only [iso.refl_inv],
  erw category.id_comp,
  rw [← iso.comp_inv_eq],
  rw [thm95.double_complex.row_map_zero_one],
  dsimp only [mul_rescale_iso_row_one, iso.trans_inv, nat_trans.comp_app, functor.map_iso_inv],
  simp only [← category.assoc, ← (BD.system κ r V r').map_comp, ← nat_trans.comp_app,
    iso.op_inv, ← op_comp, PolyhedralLattice.Cech_augmentation_map_eq_Hom_sum],
  rw [iso.comp_inv_eq],
  ext c i : 4,
  apply arrow.mk_injective,
  erw [nat_trans.comp_app, nat_trans.comp_app,
    homological_complex.comp_f, homological_complex.comp_f],
  dsimp only [BD_system_map_app_app, BD_map_app_f, data.sum_f, data.system_map, data.complex,
    data.complex₂_map_f, mul_system_iso, system_rescale_iso, complex_rescale_iso, mul_complex_iso],
  erw [nat_iso.of_components.hom_app, nat_iso.of_components.inv_app],
  dsimp only [homological_complex.hom.iso_of_components_hom_f,
    homological_complex.hom.iso_of_components_inv_f],
  dsimp only [CLCFPTinv₂, universal_map.eval_CLCFPTinv₂, CLCTinv.map_iso_hom, CLCTinv.map_iso_inv,
    CLCTinv.F_map, _root_.id, CLCTinv.map, SemiNormedGroup.equalizer.map_nat_app, unop_op],
  rw [SemiNormedGroup.equalizer.map_comp_map, SemiNormedGroup.equalizer.map_comp_map],
  apply SemiNormedGroup.equalizer.map_congr,
  { rw foo, refl },
  { rw foo, refl },
  all_goals { refl },
end

end thm95
