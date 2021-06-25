import thm95.double_complex
import rescale.Tinv
import pseudo_normed_group.sum_hom

universe variables u

noncomputable theory

open_locale nnreal

local attribute [instance] type_pow

open category_theory

namespace PolyhedralLattice

open simplex_category polyhedral_lattice (conerve.L conerve.obj)

variables (Λ : PolyhedralLattice.{u}) (N : ℕ) [fact (0 < N)]
variables (r' : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv.{u} r')


-- TODO: we probably want some efficient constructor for these isomorphisms,
-- because the default has a lot of redundancy in the proof obligations

lemma augmentation_eq_diagonal :
  cosimplicial_augmentation_map Λ N ≫ (Cech_conerve.obj_zero_iso _).hom =
  diagonal_embedding Λ N :=
by { rw ← iso.eq_comp_inv, refl }

def Hom_rescale_hom [fact (0 < r')] :
  polyhedral_lattice.Hom (rescale N Λ) M ≃+
  (ProFiltPseuNormGrpWithTinv.of r' $ (rescale N (polyhedral_lattice.Hom Λ M))) :=
add_equiv.refl _

lemma Hom_rescale_hom_symm_apply [fact (0 < r')] (x) :
  (Hom_rescale_hom Λ N r' M).symm x = x := rfl

lemma Hom_rescale_hom_strict [fact (0 < r')] (c : ℝ≥0) (f : polyhedral_lattice.Hom (rescale ↑N Λ) M) :
    f ∈ pseudo_normed_group.filtration (polyhedral_lattice.Hom (rescale ↑N Λ) M) c ↔
    f ∈ pseudo_normed_group.filtration
        (ProFiltPseuNormGrpWithTinv.of r' (rescale ↑N (polyhedral_lattice.Hom Λ M))) c :=
begin
  split,
  { intros hf c' l hl,
    rw mul_assoc,
    refine hf _,
    simp only [semi_normed_group.mem_filtration_iff],
    erw [rescale.nnnorm_def, mul_comm, div_eq_mul_inv],
    refine mul_le_mul' _ le_rfl,
    exact hl },
  { intros  hf c' l hl,
    apply pseudo_normed_group.filtration_mono (le_of_eq _),
    convert hf _,
    { exact ↑N * c' },
    { simp only [semi_normed_group.mem_filtration_iff] at hl ⊢,
      erw [rescale.nnnorm_def, div_eq_mul_inv] at hl,
      rwa [← inv_inv' (N : ℝ≥0), ← nnreal.mul_le_iff_le_inv, mul_comm],
      apply ne_of_gt,
      rw [nnreal.inv_pos],
      have hN : 0 < N := fact.out _,
      exact_mod_cast hN },
    { rw [mul_assoc, inv_mul_cancel_left'],
      have hN : 0 < N := fact.out _,
      exact_mod_cast hN.ne' } }
end

section open profinitely_filtered_pseudo_normed_group polyhedral_lattice

lemma Hom_rescale_hom_ctu [fact (0 < r')] (c : ℝ≥0) :
  continuous (pseudo_normed_group.level (Hom_rescale_hom Λ N r' M)
    (λ c f, (Hom_rescale_hom_strict Λ N r' M c f).1) c) :=
begin
  rw [add_monoid_hom.continuous_iff],
  intro l,
  haveI : fact (c * (∥l∥₊ * N⁻¹) ≤ c * N⁻¹ * ∥l∥₊) := ⟨le_of_eq $ by ring⟩,
  have aux1 := add_monoid_hom.incl_continuous (rescale N Λ) r' M c,
  have aux2 := (continuous_apply (rescale.of l)).comp aux1,
  rwa (embedding_cast_le (c * (∥l∥₊ * N⁻¹)) (c * N⁻¹ * ∥l∥₊)).continuous_iff at aux2
end

end

def Hom_rescale_iso [fact (0 < r')] :
  polyhedral_lattice.Hom (rescale N Λ) M ≅
  (ProFiltPseuNormGrpWithTinv.of r' $ (rescale N (polyhedral_lattice.Hom Λ M))) :=
@ProFiltPseuNormGrpWithTinv.iso_of_equiv_of_strict' _
  (polyhedral_lattice.Hom (rescale N Λ) M)
  (ProFiltPseuNormGrpWithTinv.of r' (rescale N (polyhedral_lattice.Hom Λ M)))
  (Hom_rescale_hom Λ N r' M)
  (by exact λ c f, Hom_rescale_hom_strict Λ N r' M c f)
  (Hom_rescale_hom_ctu Λ N r' M) (λ x, rfl)


@[simps apply symm_apply {fully_applied := ff}]
def Hom_finsupp_equiv [fact (0 < r')] :
  polyhedral_lattice.Hom (fin N →₀ Λ) M ≃+
  (ProFiltPseuNormGrpWithTinv.of r' $ ((polyhedral_lattice.Hom Λ M) ^ N)) :=
{ to_fun := λ (f : (fin N →₀ Λ) →+ M) i,
  { to_fun := λ l, f (finsupp.single i l),
    map_zero' := by rw [finsupp.single_zero, f.map_zero],
    map_add' := λ l₁ l₂, by rw [finsupp.single_add, f.map_add] },
  map_add' := λ f g,
    by { ext i l, simp only [add_monoid_hom.add_apply, add_monoid_hom.coe_mk, pi.add_apply] },
  inv_fun := λ (f : (Λ →+ M) ^ N),
  { to_fun := λ x, x.sum $ λ i l, f i l,
    map_zero' := by rw [finsupp.sum_zero_index],
    map_add' := λ x y, by simp only [finsupp.sum_add_index'] },
  left_inv := λ f,
  begin
    ext i l, dsimp only,
    simp only [add_monoid_hom.coe_comp, add_monoid_hom.coe_mk, add_monoid_hom.to_fun_eq_coe,
      finsupp.single_add_hom_apply, function.comp_app, add_monoid_hom.map_zero,
      finsupp.sum_single_index],
    erw [finsupp.sum_single_index],
    rw [finsupp.single_zero, add_monoid_hom.map_zero],
  end,
  right_inv := λ f,
  begin
    ext i l, dsimp only,
    simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.coe_mk,
      finsupp.sum_single_index, add_monoid_hom.map_zero],
  end }
.

section open profinitely_filtered_pseudo_normed_group polyhedral_lattice pseudo_normed_group

lemma Hom_finsupp_equiv_strict [fact (0 < r')]
  (c : ℝ≥0) (f : (polyhedral_lattice.Hom (fin N →₀ Λ) M)) :
  f ∈ filtration (polyhedral_lattice.Hom (fin N →₀ Λ) M) c ↔
  (Λ.Hom_finsupp_equiv N r' M) f ∈ filtration
    (ProFiltPseuNormGrpWithTinv.of r' ((polyhedral_lattice.Hom Λ M) ^ N)) c :=
begin
  split,
  { intros hf i c' l hl,
    refine hf _,
    rw [semi_normed_group.mem_filtration_iff, finsupp.nnnorm_def, finsupp.sum_single_index],
    { exact hl },
    { exact nnnorm_zero } },
  { intros hf c' l hl,
    let g := (Λ.Hom_finsupp_equiv N r' M) f,
    have hg : (Λ.Hom_finsupp_equiv N r' M).symm g = f := add_equiv.symm_apply_apply _ _,
    rw [semi_normed_group.mem_filtration_iff, finsupp.nnnorm_def, finsupp.sum_fintype] at hl,
    swap, { intro, exact nnnorm_zero },
    rw [← hg, Hom_finsupp_equiv_symm_apply, add_monoid_hom.coe_mk, finsupp.sum_fintype],
    swap, { intro, exact add_monoid_hom.map_zero _ },
    apply filtration_mono (mul_le_mul' le_rfl hl),
    rw [finset.mul_sum],
    apply sum_mem_filtration,
    rintro i hi,
    apply hf _,
    rw semi_normed_group.mem_filtration_iff, }
end

lemma Hom_finsupp_equiv_ctu [fact (0 < r')] (c : ℝ≥0) :
  continuous (level (Λ.Hom_finsupp_equiv N r' M)
    (λ c x, (Hom_finsupp_equiv_strict Λ N r' M c x).1) c) :=
begin
  apply continuous_induced_rng,
  rw continuous_pi_iff,
  intro i,
  dsimp only [function.comp],
  rw add_monoid_hom.continuous_iff,
  intro l,
  haveI : fact (c * ∥finsupp.single i l∥₊ ≤ c * ∥l∥₊) := ⟨mul_le_mul' le_rfl $ le_of_eq _⟩,
  { have aux1 := add_monoid_hom.incl_continuous (fin N →₀ Λ) r' M c,
    have aux2 := (continuous_apply (finsupp.single i l)).comp aux1,
    rwa (embedding_cast_le (c * ∥finsupp.single i l∥₊) (c * ∥l∥₊)).continuous_iff at aux2 },
  { rw [finsupp.nnnorm_def, finsupp.sum_single_index], exact nnnorm_zero }
end

end

@[simps]
def Hom_finsupp_iso [fact (0 < r')] :
  polyhedral_lattice.Hom (fin N →₀ Λ) M ≅
  (ProFiltPseuNormGrpWithTinv.of r' $ ((polyhedral_lattice.Hom Λ M) ^ N)) :=
ProFiltPseuNormGrpWithTinv.iso_of_equiv_of_strict' (Hom_finsupp_equiv _ _ _ _)
  (Hom_finsupp_equiv_strict Λ N r' M) (Hom_finsupp_equiv_ctu Λ N r' M)
  (by { intro, ext1, refl })
.

open opposite

section

variables [fact (0 < r')] (N' : ℝ≥0)

def Hom_cosimplicial_zero_iso' :
  (Hom M).obj (op $ of $ rescale N (of (fin N →₀ Λ))) ≅
  (Hom M).obj (op $ (Λ.cosimplicial N).obj (mk 0)) :=
(Hom M).map_iso $ (Cech_conerve.obj_zero_iso _).op

def Hom_cosimplicial_zero_iso_aux (h : N' = N) :
  ProFiltPseuNormGrpWithTinv.of r' (rescale N (polyhedral_lattice.Hom Λ M)) ≅
  (ProFiltPseuNormGrpWithTinv.rescale r' N').obj (polyhedral_lattice.Hom Λ M) :=
begin
  rw h, exact iso.refl _
end

@[simp] lemma Hom_cosimplicial_zero_iso_aux_rfl :
  Hom_cosimplicial_zero_iso_aux Λ N r' M N rfl = iso.refl _ := rfl

def Hom_cosimplicial_zero_iso (h : N' = N) :
  polyhedral_lattice.Hom ((Λ.cosimplicial N).obj (simplex_category.mk 0)) M ≅
  (ProFiltPseuNormGrpWithTinv.of r' (rescale N' ((polyhedral_lattice.Hom Λ M) ^ N))) :=
(Hom_cosimplicial_zero_iso' Λ N r' M).symm ≪≫
/- jmc is not very proud of this -/
(by exact iso.refl _ : _) ≪≫
(Hom_rescale_iso (of (fin N →₀ Λ)) N r' M) ≪≫
Hom_cosimplicial_zero_iso_aux _ _ _ _ _ h ≪≫
(ProFiltPseuNormGrpWithTinv.rescale r' N').map_iso (Hom_finsupp_iso Λ N r' M)

end

variables [fact (0 < r')] [fact (r' ≤ 1)]

open_locale big_operators

def unrescale (N : ℝ≥0) (M : Type*) [profinitely_filtered_pseudo_normed_group M] :
  profinitely_filtered_pseudo_normed_group_hom (rescale N M) M :=
profinitely_filtered_pseudo_normed_group_hom.mk_of_bound (add_monoid_hom.id _) N⁻¹
begin
  intro c,
  refine ⟨λ x hx, _, _⟩,
  { rwa mul_comm },
  { haveI : fact (c * N⁻¹ ≤ N⁻¹ * c) := ⟨(mul_comm _ _).le⟩,
    exact profinitely_filtered_pseudo_normed_group.continuous_cast_le (c * N⁻¹) (N⁻¹ * c) },
end

def rescale_proj (N : ℕ) (M : Type*) [profinitely_filtered_pseudo_normed_group M] (i : fin N) :
  profinitely_filtered_pseudo_normed_group_hom (rescale N (M ^ N)) M :=
(profinitely_filtered_pseudo_normed_group.pi_proj i).comp (unrescale N _)

lemma rescale_proj_bound_by
  (N : ℕ) (M : Type*) [profinitely_filtered_pseudo_normed_group M] (i : fin N) :
  (rescale_proj N M i).bound_by N⁻¹ :=
by { intros c x hx, rw [rescale.mem_filtration, mul_comm] at hx, exact hx i }

def Hom_sum :
  ProFiltPseuNormGrpWithTinv.of r' (rescale N ((Λ →+ M) ^ N)) ⟶
  ProFiltPseuNormGrpWithTinv.of r' (Λ →+ M) :=
profinitely_filtered_pseudo_normed_group_with_Tinv.sum_hom (Λ →+ M) N

lemma Hom_sum_apply (x) : Hom_sum Λ N r' M x = ∑ i, x i :=
profinitely_filtered_pseudo_normed_group_with_Tinv.sum_hom_apply _ _ _

lemma finsupp_sum_diagonal_embedding (f : (Λ →+ M) ^ N) (l : Λ) :
  finsupp.sum ((Λ.diagonal_embedding N) l) (λ i, (f i)) =
  (show Λ → M, from show Λ →+ M, from Λ.Hom_sum N r' M f) l :=
begin
  simp only [add_monoid_hom.coe_mk, Hom_sum_apply],
  rw [finsupp.sum_fintype, add_monoid_hom.finset_sum_apply, fintype.sum_congr],
  { intro i,
    dsimp only [diagonal_embedding, polyhedral_lattice_hom.coe_mk, finsupp.single_add_hom_apply,
      rescale.of, equiv.coe_refl, id],
    simp only [finset.sum_apply', finsupp.single_apply, finset.sum_ite_eq', finset.mem_univ, if_true], },
  { intro i, exact (f i).map_zero }
end

lemma Cech_augmentation_map_eq_Hom_sum :
  (Λ.Hom_cosimplicial_zero_iso N r' M ↑N rfl).inv ≫ (thm95.Cech_augmentation_map r' Λ M N) =
  (Hom_sum Λ N r' M) :=
begin
  dsimp only [thm95.Cech_augmentation_map, Hom_cosimplicial_zero_iso,
    Hom_cosimplicial_zero_iso_aux_rfl, Hom_cosimplicial_zero_iso'],
  rw [iso.refl_trans, iso.refl_trans],
  dsimp only [iso.trans_inv, functor.map_iso_hom, functor.map_iso_inv, iso.symm_inv, op_comp],
  simp only [category.assoc, ← (Hom M).map_comp, augmentation_eq_diagonal, iso.op_hom, ← op_comp],
  dsimp only [Hom_rescale_iso, Hom_finsupp_iso],
  ext f l : 2,
  exact finsupp_sum_diagonal_embedding Λ N r' M f l,
end

end PolyhedralLattice
