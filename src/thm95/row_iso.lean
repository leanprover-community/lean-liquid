import thm95.polyhedral_iso
import pseudo_normed_group.homotopy
import rescale.FiltrationPow

/-!
# A complex canonically isomorphic to `row 1` of the double complex

We have
```
lemma double_complex.row_one :
  (double_complex BD c' r r' V Λ M N).row 1 =
  BD.system c' r V r' (Hom ((cosimplicial Λ N).obj (mk 0)) M) := rfl
```

We want to "rewrite" this row in such a way that it is the target
of the homotopies that will be constructed formally from `BD.homotopy`.

Concretely, we want:
```
(((data.mul N).obj BD.data).system (rescale_constants c_ N) r V r').obj (op (Hom Λ M)) ≅
  (thm95.double_complex BD.data c_ r r' V Λ M N).row 1
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

open_locale nnreal

local attribute [instance] type_pow

local attribute [reducible] CLCFPTinv₂ CLCFPTinv₂.res
  breen_deligne.universal_map.eval_CLCFPTinv₂

open category_theory

section rescale

variables {BD : breen_deligne.data}
variables (c_ c_₁ c_₂ : ℕ → ℝ≥0)
variables [BD.suitable c_]
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)] (c : ℝ≥0)
variables (M : ProFiltPseuNormGrpWithTinv.{u} r')

-- move this
instance rescale_constants_suitable (N : ℝ≥0) :
  BD.suitable (rescale_constants c_ N) :=
by { delta rescale_constants, apply_instance }

variables (BD)

open breen_deligne opposite ProFiltPseuNormGrpWithTinv (of)

-- this is not `iso.refl` -- so close, and yet so far away
-- the difference is `M_{(c * c_i) * N⁻¹}` vs `M_{c * (c_i * N⁻¹)}`
lemma complex_rescale_eq (N : ℝ≥0) :
  (BD.complex (rescale_constants c_ N) r V r' c).obj (op M) =
  (BD.complex c_ r V r' c).obj (op $ of r' $ rescale N M) :=
begin
  dsimp only [data.complex, rescale_constants],
  haveI : ∀ c c_, fact (c * c_ * N⁻¹ ≤ c * (c_ * N⁻¹)) :=
    λ c c_, by simpa only [mul_assoc] using nnreal.fact_le_refl _,
  transitivity
    (BD.complex₂ r V r' (λ (i : ℕ), c * c_ i * N⁻¹) (λ (i : ℕ), r' * (c * c_ i) * N⁻¹)).obj (op M),
  { simp only [mul_assoc, ProFiltPseuNormGrpWithTinv.of_coe] },
  refine cochain_complex.ext (λ i, _),
  dsimp only [data.complex₂, rescale_constants, data.complex₂_d],
  rw universal_map.eval_CLCFPTinv₂_rescale,
end
.

section

def complex_rescale_iso (N : ℝ≥0) :
  (BD.complex (rescale_constants c_ N) r V r' c).obj (op M) ≅
  (BD.complex c_ r V r' c).obj (op $ of r' $ rescale N M) :=
differential_object.complex_like.iso_of_components
begin
  intro i,
  refine CLCTinv.map_iso r V _ _ _ _ _ _ _ _,
  { refine ((Pow $ BD.X i).map_iso _).op, exact Filtration_cast_eq r' _ _ (mul_assoc _ _ _) M, },
  { refine ((Pow $ BD.X i).map_iso _).op,
    exact (Filtration_cast_eq _ (r' * (c * c_ i) * N⁻¹) (r' * (c * (c_ i * N⁻¹)))
      (by simp only [mul_assoc]) _) },
  { refl },
  { refl }
end
begin
  intros i j,
  apply arrow.mk_inj,
  dsimp only [data.complex_obj_d, universal_map.eval_CLCFPTinv, universal_map.eval_CLCFPTinv₂,
    _root_.id, NormedGroup.equalizer.map_nat_app, CLCTinv.map_iso_hom, CLCTinv.map],
  simp only [NormedGroup.equalizer.map_comp_map,
    universal_map.eval_CLCFP_rescale, ← CLCFP.res_def'],
  apply NormedGroup.equalizer.map_congr,
  { have := @universal_map.res_comp_eval_CLCFP V r'
      (c * (c_ i * N⁻¹)) (c * c_ i * N⁻¹) (c * (c_ j * N⁻¹)) (c * c_ j * N⁻¹)
      (BD.X j) (BD.X i) (BD.d j i) ⟨(mul_assoc _ _ _).le⟩ _ _ ⟨(mul_assoc _ _ _).le⟩,
    replace := nat_trans.congr_app this.symm (op M),
    exact congr_arg arrow.mk this },
  { have := @universal_map.res_comp_eval_CLCFP V r'
      (r' * (c * (c_ i * N⁻¹))) (r' * (c * c_ i) * N⁻¹) (r' * (c * (c_ j * N⁻¹))) (r' * (c * c_ j) * N⁻¹)
      (BD.X j) (BD.X i) (BD.d j i) ⟨le_of_eq $ by simp only [mul_assoc]⟩ _ _ ⟨le_of_eq $ by simp only [mul_assoc]⟩,
    replace := nat_trans.congr_app this.symm (op M),
    exact congr_arg arrow.mk this },
  any_goals { refl },
end
.

noncomputable
def system_rescale_iso (N : ℝ≥0) :
  (BD.system (rescale_constants c_ N) r V r').obj (op M) ≅
  (BD.system c_ r V r').obj (op $ of r' $ rescale N M) :=
nat_iso.of_components (λ c, complex_rescale_iso BD c_ r V c.unop _ _)
begin
  intros c₁ c₂ h,
  ext i : 2,
  apply arrow.mk_inj,
  erw [differential_object.comp_f, differential_object.comp_f],
  dsimp only [data.system_obj, differential_object.hom.mk'_f, CLCFPTinv₂.res, complex_rescale_iso,
    differential_object.complex_like.iso_of_components, CLCTinv.map_iso_hom, CLCTinv.map_nat_app],
  simp only [CLCTinv.map_comp_map],
  refl,
end

end

end rescale

namespace thm95

open breen_deligne polyhedral_lattice opposite

variables (BD : breen_deligne.data) (c_ : ℕ → ℝ≥0) [BD.suitable c_]
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
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
  dsimp [universal_map.eval_CLCFP],
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
  (((data.mul N).obj BD).complex c_ r V r' c).obj (op M) ≅
  (BD.complex c_ r V r' c).obj (op (ProFiltPseuNormGrpWithTinv.of r' $ M^N)) :=
differential_object.complex_like.iso_of_components
begin
  intro i,
  refine CLCTinv.map_iso r V _ _ _ _ _ _ _ _,
  { exact (FiltrationPow.mul_iso.{u u} r' (c * c_ i) M N (BD.X i)).op },
  { exact (FiltrationPow.mul_iso.{u u} r' (r' * (c * c_ i)) M N (BD.X i)).op },
  { refl },
  { refl }
end
begin
  intros i j,
  apply arrow.mk_inj,
  dsimp only [data.complex_obj_d, universal_map.eval_CLCFPTinv, universal_map.eval_CLCFPTinv₂,
    _root_.id, NormedGroup.equalizer.map_nat_app, CLCTinv.map_iso_hom, CLCTinv.map,
    data.mul_obj_d],
  simp only [NormedGroup.equalizer.map_comp_map],
  apply NormedGroup.equalizer.map_congr,
  { rw eval_CLCFP_mul },
  { rw eval_CLCFP_mul },
  all_goals { refl }
end

end

def mul_system_iso (N : ℕ) [fact (0 < N)] (M : ProFiltPseuNormGrpWithTinv.{u} r') :
  (((data.mul N).obj BD).system c_ r V r').obj (op M) ≅
  (BD.system c_ r V r').obj (op (ProFiltPseuNormGrpWithTinv.of r' $ M^N)) :=
nat_iso.of_components (λ c, mul_complex_iso BD c_ r V N M c.unop)
begin
  intros c₁ c₂ hc,
  ext i : 2,
  apply arrow.mk_inj,
  erw [differential_object.comp_f, differential_object.comp_f],
  dsimp only [data.system_obj, differential_object.hom.mk'_f, CLCFPTinv₂.res, mul_complex_iso,
    differential_object.complex_like.iso_of_components, CLCTinv.map_iso_hom, CLCTinv.map_nat_app],
  simp only [CLCTinv.map_comp_map],
  refl,
end

def mul_rescale_iso_row_one
  (N : ℕ) [fact (0 < N)] (N' : ℝ≥0) (h : N' = N)
  (Λ : PolyhedralLattice) (M : ProFiltPseuNormGrpWithTinv.{u} r') :
  (((data.mul N).obj BD).system (rescale_constants c_ N') r V r').obj (op (Hom Λ M)) ≅
    ((thm95.double_complex BD c_ r r' V Λ M N).row 1) :=
(mul_system_iso _ _ r V N _) ≪≫
(system_rescale_iso _ c_ r V _ _) ≪≫
((BD.system c_ r V r').map_iso $
  (PolyhedralLattice.Hom_cosimplicial_zero_iso Λ N r' M N' h).op)

lemma mul_rescale_iso_row_one_strict
  (N : ℕ) [fact (0 < N)] (N' : ℝ≥0) (h : N' = N)
  (Λ : PolyhedralLattice) (M : ProFiltPseuNormGrpWithTinv.{u} r')
  (c : ℝ≥0) (i : ℕ)
  (x : (((data.mul N).obj BD).system (rescale_constants c_ N') r V r').obj (op (Hom Λ M)) c i) :
  ∥(mul_rescale_iso_row_one BD c_ r V N N' h Λ M).hom x∥ = ∥x∥ :=
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
begin
  dsimp only [universal_map.sum],
  rw [@universal_map.eval_CLCFP_of _ _ _ _ _ _ _ _, whisker_right_app, nat_trans.op_app],
  refl
end

lemma bar (N : ℕ) [fact (0 < N)] (Λ : PolyhedralLattice) (M : ProFiltPseuNormGrpWithTinv.{u} r')
  (c₁ c₂ : ℝ≥0) (hc : c₁ * N⁻¹ = c₂) (n : ℕ)
  {_ : ((finset.univ : finset (fin N)).sum (basic_universal_map.proj n)).suitable c₂ c₁} :
  (Pow n).map (((Filtration r').map (eq_to_iso hc).inv).app (ProFiltPseuNormGrpWithTinv.of r' (↥(Hom ↥Λ ↥M) ^ N)) ≫ ((Filtration r').obj c₁).map (Λ.Hom_sum N r' M).op.unop) =
  (FiltrationPow.mul_iso r' c₂ (Hom ↥Λ ↥M) N n).hom ≫ (basic_universal_map.eval_FP r' c₂ c₁ (finset.univ.sum (basic_universal_map.proj n))).app (Hom ↥Λ ↥M) :=
begin
  ext x i : 3,
  dsimp only [Pow_obj, Filtration_obj_obj, Profinite.of, Top.coe_of, Hom,
    ProFiltPseuNormGrpWithTinv.coe_of] at x,
  erw [coe_comp, (Pow n).map_comp, coe_comp],
  dsimp only [FiltrationPow.mul_iso_hom],
  erw [coe_comp],
  dsimp only [Pow_map, continuous_map.coe_mk, quiver.hom.unop_op, Filtration_map_app,
    profinitely_filtered_pseudo_normed_group_with_Tinv_hom.level, pseudo_normed_group.level,
    Filtration_obj_map_to_fun, subtype.coe_mk, Filtration.cast_le_to_fun,
     pseudo_normed_group.coe_cast_le, basic_universal_map.eval_FP, basic_universal_map.eval_png₀],
  rw [basic_universal_map.eval_png_sum, PolyhedralLattice.Hom_sum_apply,
      add_monoid_hom.finset_sum_apply, finset.sum_apply],
  apply fintype.sum_congr,
  intro j,
  rw [basic_universal_map.eval_png_apply, Pow_Pow_X_hom_to_fun, Filtration.pi_iso],
  erw [Profinite.iso_of_homeo_hom],
  dsimp only [function.uncurry, continuous_map.coe_mk, equiv.arrow_congr_apply,
    pseudo_normed_group.pow_incl_apply, basic_universal_map.proj, function.comp,
    profinitely_filtered_pseudo_normed_group.filtration_pi_homeo_apply],
  rw [← fin_prod_fin_equiv.sum_comp], swap, { apply_instance },
  simp only [
    matrix.reindex_linear_equiv_apply, matrix.reindex_apply, matrix.minor_apply,
    equiv.punit_prod_symm_apply, matrix.kronecker, matrix.one_apply,
    basic_universal_map.proj_aux, equiv.symm_apply_apply,
    boole_mul, ← ite_and, @eq_comm _ i],
  simp only [← prod.mk.inj_iff, ite_smul, one_smul, zero_smul, prod.mk.eta],
  simp only [equiv.arrow_congr_apply, equiv.refl_apply, subtype.coe_mk,
    equiv.symm_trans_apply,  equiv.symm_apply_apply],
  convert (finset.sum_ite_eq' finset.univ (j, i) (λ p, (x p.2).val p.1)).symm using 1,
  { simp only [finset.mem_univ, if_true, subtype.val_eq_coe], },
  { apply fintype.sum_congr,
    rintro ⟨a, b⟩,
    simp only [equiv.prod_comm_symm, equiv.prod_comm_apply, prod.fst_swap, prod.snd_swap],
    split_ifs; refl }
end

lemma foo (N : ℕ) [fact (0 < N)] (Λ : PolyhedralLattice) (M : ProFiltPseuNormGrpWithTinv.{u} r')
  (c₁ c₂ : ℝ≥0) (hc : c₁ * N⁻¹ = c₂) (i : ℕ) [H : universal_map.suitable c₂ c₁ (universal_map.sum i N)] :
  ((CLC V).map ((FiltrationPow r' c₁ i).op.map (Λ.Hom_sum N r' M).op) ≫ (CLC V).map ((Pow i).map_iso (Filtration_cast_eq r' (c₁ * N⁻¹) c₂ hc (ProFiltPseuNormGrpWithTinv.of r' ((Hom Λ M) ^ N)))).op.inv) =
  ((universal_map.eval_CLCFP V r' c₁ c₂ (universal_map.sum i N)).app (op (Hom Λ M)) ≫ (CLC V).map (FiltrationPow.mul_iso r' c₂ (Hom Λ M) N i).op.hom) :=
begin
  rw [← (CLC V).map_comp],
  dsimp only [FiltrationPow, category_theory.functor.op_map, category_theory.functor.comp_map,
    Filtration_cast_eq],
  rw [iso.op_inv, ← op_comp, functor.map_iso_inv, ← (Pow i).map_comp, nat_iso.app_inv,
    functor.map_iso_inv, quux, ← (CLC V).map_comp, iso.op_hom, ← op_comp],
  swap, { exact @basic_universal_map.suitable_of_suitable_of _ _ _ _ _ H },
  congr' 2,
  apply bar,
end

lemma row_map_eq_sum_comp
  (N : ℕ) [fact (0 < N)] (N' : ℝ≥0) (h : N' = N)
  [∀ (i : ℕ), universal_map.suitable (rescale_constants c_ N' i) (c_ i) ((BD.sum N).f i)]
  (Λ : PolyhedralLattice) (M : ProFiltPseuNormGrpWithTinv.{u} r') :
  (thm95.double_complex BD c_ r r' V Λ M N).row_map 0 1 =
    (iso.refl ((BD.system c_ r V r').obj (op (Hom Λ M)))).inv ≫
    (BD_system_map (BD.sum N) c_
      (rescale_constants c_ N') r V).app (op (Hom Λ M)) ≫
    (thm95.mul_rescale_iso_row_one BD c_ r V N N' h Λ M).hom :=
begin
  unfreezingI { subst h },
  dsimp only [iso.refl_inv],
  erw category.id_comp,
  rw [← iso.comp_inv_eq],
  rw [thm95.double_complex.row_map_zero_one],
  dsimp only [mul_rescale_iso_row_one, iso.trans_inv, nat_trans.comp_app, functor.map_iso_inv],
  simp only [← category.assoc, ← (BD.system c_ r V r').map_comp, ← nat_trans.comp_app,
    PolyhedralLattice.Cech_augmentation_map_eq_Hom_sum],
  rw [iso.comp_inv_eq],
  ext c i : 4,
  apply arrow.mk_inj,
  erw [nat_trans.comp_app, nat_trans.comp_app,
    differential_object.comp_f, differential_object.comp_f],
  dsimp only [BD_system_map_app_app, BD_map_app_f, data.sum_f, data.system_map, data.complex,
    data.complex₂_map_f, mul_system_iso, system_rescale_iso, complex_rescale_iso, mul_complex_iso],
  erw [nat_iso.of_components.hom_app, nat_iso.of_components.inv_app],
  dsimp only [differential_object.complex_like.iso_of_components_hom_f,
    differential_object.complex_like.iso_of_components_inv_f],
  dsimp only [CLCFPTinv₂, universal_map.eval_CLCFPTinv₂, CLCTinv.map_iso_hom, CLCTinv.map_iso_inv,
    CLCTinv.F_map, _root_.id, CLCTinv.map, NormedGroup.equalizer.map_nat_app],
  rw [NormedGroup.equalizer.map_comp_map, NormedGroup.equalizer.map_comp_map],
  apply NormedGroup.equalizer.map_congr,
  { rw foo, refl },
  { rw foo, refl },
  all_goals { refl },
end

end thm95
