import thm95.double_complex
import rescale.Tinv

import for_mathlib.category

universe variables u

noncomputable theory

open_locale nnreal

local attribute [instance] type_pow

open category_theory

namespace PolyhedralLattice

open simplex_category polyhedral_lattice (conerve.L conerve.obj)

variables (Λ : PolyhedralLattice) (N : ℕ) [fact (0 < N)]
variables (r' : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv r')


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

lemma Hom_rescale_hom_strict [fact (0 < r')] (c : ℝ≥0) (f : polyhedral_lattice.Hom (rescale ↑N ↥Λ) ↥M) :
    f ∈ pseudo_normed_group.filtration ↥(polyhedral_lattice.Hom (rescale ↑N ↥Λ) ↥M) c ↔
    f ∈ pseudo_normed_group.filtration
        ↥(ProFiltPseuNormGrpWithTinv.of r' (rescale ↑N ↥(polyhedral_lattice.Hom ↥Λ ↥M))) c :=
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
  haveI : fact (c * (nnnorm l * N⁻¹) ≤ c * N⁻¹ * nnnorm l) := ⟨le_of_eq $ by ring⟩,
  have aux1 := add_monoid_hom.incl_continuous (rescale N Λ) r' M c,
  have aux2 := (continuous_apply (rescale.of l)).comp aux1,
  rwa (embedding_cast_le (c * (nnnorm l * N⁻¹)) (c * N⁻¹ * nnnorm l)).continuous_iff at aux2
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
{ to_fun := λ (f : (fin N →₀ ↥Λ) →+ ↥M) i,
  { to_fun := λ l, f (finsupp.single i l),
    map_zero' := by rw [finsupp.single_zero, f.map_zero],
    map_add' := λ l₁ l₂, by rw [finsupp.single_add, f.map_add] },
  map_add' := λ f g, by { ext i l, simp only [add_monoid_hom.coe_add, add_monoid_hom.coe_mk, pi.add_apply] },
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
  f ∈ filtration (polyhedral_lattice.Hom (fin N →₀ ↥Λ) M) c ↔
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
    rw [semi_normed_group.mem_filtration_iff, finsupp.nnnorm_def, finsupp.sum_eq_sum_fintype] at hl,
    swap, { intro, exact nnnorm_zero },
    rw [← hg, Hom_finsupp_equiv_symm_apply, add_monoid_hom.coe_mk, finsupp.sum_eq_sum_fintype],
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
  haveI : fact (c * nnnorm (finsupp.single i l) ≤ c * nnnorm l) := ⟨mul_le_mul' le_rfl $ le_of_eq _⟩,
  { have aux1 := add_monoid_hom.incl_continuous (fin N →₀ Λ) r' M c,
    have aux2 := (continuous_apply (finsupp.single i l)).comp aux1,
    rwa (embedding_cast_le (c * nnnorm (finsupp.single i l)) (c * nnnorm l)).continuous_iff at aux2 },
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
  (Hom M).obj (of $ rescale N (of (fin N →₀ Λ))) ≅
  (Hom M).obj ((Λ.cosimplicial N).obj (mk 0)) :=
(Hom M).map_iso $ (Cech_conerve.obj_zero_iso _).symm

def Hom_cosimplicial_zero_iso_aux (h : N' = N) :
  ProFiltPseuNormGrpWithTinv.of r' (rescale N (polyhedral_lattice.Hom Λ M)) ≅
  (ProFiltPseuNormGrpWithTinv.rescale r' N').obj (polyhedral_lattice.Hom Λ M) :=
begin
  rw h, exact iso.refl _
end

def Hom_cosimplicial_zero_iso (h : N' = N) :
  polyhedral_lattice.Hom ((Λ.cosimplicial N).obj (simplex_category.mk 0)) M ≅
  (ProFiltPseuNormGrpWithTinv.of r' (rescale N' ((polyhedral_lattice.Hom Λ M) ^ N))) :=
(Hom_cosimplicial_zero_iso' Λ N r' M).unop ≪≫
/- jmc is not very proud of this -/
(by exact iso.refl _ : _) ≪≫
(Hom_rescale_iso (of (fin N →₀ ↥Λ)) N r' M) ≪≫
Hom_cosimplicial_zero_iso_aux _ _ _ _ _ h ≪≫
(ProFiltPseuNormGrpWithTinv.rescale r' N').map_iso (Hom_finsupp_iso Λ N r' M)

end

end PolyhedralLattice
