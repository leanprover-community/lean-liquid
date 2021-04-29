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

def finsupp_fin_one_iso : of (fin 1 →₀ Λ) ≅ Λ :=
iso.symm $ PolyhedralLattice.iso_mk
  (finsupp.single_add_hom 0) (finsupp.apply_add_hom 0)
  (λ l, by { dsimp [finsupp.norm_def], simp only [norm_zero, finsupp.sum_single_index] })
  (by { ext l, dsimp, simp only [finsupp.single_eq_same] })
  (by { ext f x, fin_cases x, dsimp, simp only [finsupp.single_eq_same] })
.

/-- the left hand side is by definition the quotient of the right hand side
by a subgroup that is provably trivial -/
noncomputable def conerve_obj_one_iso' :
  of (conerve.obj (diagonal_embedding Λ N) 1) ≅ of (fin 1 →₀ (rescale N (fin N →₀ Λ))) :=
iso.symm $ PolyhedralLattice.iso_mk
  (polyhedral_lattice.conerve.π _ _)
  (quotient_add_group.lift _ (add_monoid_hom.id _)
    (by { intros x hx, rwa [polyhedral_lattice.conerve.L_one, add_subgroup.mem_bot] at hx }))
  (polyhedral_lattice.conerve.norm_π_one_eq _)
  (by ext; refl) (by ext ⟨x⟩; refl)

noncomputable def conerve_obj_one_iso :
  of (conerve.obj (diagonal_embedding Λ N) 1) ≅ of (rescale N (fin N →₀ Λ)) :=
conerve_obj_one_iso' Λ N ≪≫ finsupp_fin_one_iso (of (rescale N (fin N →₀ Λ)))

lemma augmentation_eq_diagonal :
  cosimplicial_augmentation_map Λ N ≫ (conerve_obj_one_iso Λ N).hom =
  diagonal_embedding Λ N :=
by { rw ← iso.eq_comp_inv, refl }

def Hom_rescale_hom [fact (0 < r')] :
  polyhedral_lattice.Hom (rescale N Λ) M ≃+
  (ProFiltPseuNormGrpWithTinv.of r' $ (rescale N (polyhedral_lattice.Hom Λ M))) :=
add_equiv.refl _

lemma foo [fact (0 < r')] (c : ℝ≥0) (f : polyhedral_lattice.Hom (rescale ↑N ↥Λ) ↥M) :
    f ∈ pseudo_normed_group.filtration ↥(polyhedral_lattice.Hom (rescale ↑N ↥Λ) ↥M) c ↔
    f ∈
      pseudo_normed_group.filtration
        ↥(ProFiltPseuNormGrpWithTinv.of r' (rescale ↑N ↥(polyhedral_lattice.Hom ↥Λ ↥M)))
        c :=
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

lemma bar [fact (0 < r')] (c : ℝ≥0) :
  continuous (pseudo_normed_group.level (Hom_rescale_hom Λ N r' M) (λ c f, (foo Λ N r' M c f).1) c) := sorry

def Hom_rescale_iso [fact (0 < r')] :
  polyhedral_lattice.Hom (rescale N Λ) M ≅
  (ProFiltPseuNormGrpWithTinv.of r' $ (rescale N (polyhedral_lattice.Hom Λ M))) :=
@ProFiltPseuNormGrpWithTinv.iso_of_equiv_of_strict' _
  (polyhedral_lattice.Hom (rescale N Λ) M)
  (ProFiltPseuNormGrpWithTinv.of r' (rescale N (polyhedral_lattice.Hom Λ M)))
  (Hom_rescale_hom Λ N r' M)
  (by exact λ c f, (foo Λ N r' M c f).1)
  (bar Λ N r' M) (λ x, rfl)
  (by exact λ c f, (foo Λ N r' M c f).2)

@[simps]
def Hom_finsupp_iso_hom' [fact (0 < r')] :
  polyhedral_lattice.Hom (fin N →₀ Λ) M →+
  (ProFiltPseuNormGrpWithTinv.of r' $ ((polyhedral_lattice.Hom Λ M) ^ N)) :=
{ to_fun := λ (f : (fin N →₀ ↥Λ) →+ ↥M) i,
  { to_fun := λ l, f (finsupp.single i l),
    map_zero' := by rw [finsupp.single_zero, f.map_zero],
    map_add' := λ l₁ l₂, by rw [finsupp.single_add, f.map_add] },
  map_zero' := by { ext i l, simp only [pi.zero_apply, add_monoid_hom.coe_zero, add_monoid_hom.coe_mk] },
  map_add' := λ f g, by { ext i l, simp only [add_monoid_hom.coe_add, add_monoid_hom.coe_mk, pi.add_apply] } }
.

@[simps]
def Hom_finsupp_iso_hom [fact (0 < r')] :
  polyhedral_lattice.Hom (fin N →₀ Λ) M ⟶
  (ProFiltPseuNormGrpWithTinv.of r' $ ((polyhedral_lattice.Hom Λ M) ^ N)) :=
{ strict' := sorry,
  continuous' := sorry,
  map_Tinv' := sorry,
  .. Hom_finsupp_iso_hom' Λ N r' M }
.

@[simps]
def Hom_finsupp_equiv [fact (0 < r')] :
  polyhedral_lattice.Hom (fin N →₀ Λ) M ≃+
  (ProFiltPseuNormGrpWithTinv.of r' $ ((polyhedral_lattice.Hom Λ M) ^ N)) :=
{ inv_fun := λ (f : (Λ →+ M) ^ N),
  { to_fun := λ x, x.sum $ λ i l, f i l,
    map_zero' := by rw [finsupp.sum_zero_index],
    map_add' := λ x y, by simp only [finsupp.sum_add_index'] },
  left_inv := λ f,
  begin
    ext i l,
    simp only [add_monoid_hom.coe_comp, add_monoid_hom.coe_mk, add_monoid_hom.to_fun_eq_coe,
     finsupp.single_add_hom_apply, function.comp_app, finsupp.sum_single_index,
     add_monoid_hom.map_zero],
    refl
  end,
  right_inv := λ f,
  begin
    ext i l,
    simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.coe_mk, Hom_finsupp_iso_hom'_apply_apply,
      finsupp.sum_single_index, add_monoid_hom.map_zero],
  end,
  .. Hom_finsupp_iso_hom' Λ N r' M }
.

@[simps]
def Hom_finsupp_iso [fact (0 < r')] :
  polyhedral_lattice.Hom (fin N →₀ Λ) M ≅
  (ProFiltPseuNormGrpWithTinv.of r' $ ((polyhedral_lattice.Hom Λ M) ^ N)) :=
@ProFiltPseuNormGrpWithTinv.iso_of_equiv_of_strict _ _ _
  (Hom_finsupp_iso_hom _ _ _ _) (Hom_finsupp_equiv _ _ _ _) (λ _, rfl) sorry
.

open opposite

section

variables [fact (0 < r')] (N' : ℝ≥0)

def Hom_cosimplicial_zero_iso' :
  (Hom M).obj (of $ rescale N (of (fin N →₀ Λ))) ≅
  (Hom M).obj ((Λ.cosimplicial N).obj (mk 0)) :=
(Hom M).map_iso $ (conerve_obj_one_iso _ _).symm

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
