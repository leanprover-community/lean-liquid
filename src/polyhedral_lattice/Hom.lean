import polyhedral_lattice.pseudo_normed_group
import polyhedral_lattice.int
import polyhedral_lattice.category
import pseudo_normed_group.category

/-!

# Category-theoretic Hom(Λ, M)

If Λ is a polyhedral lattice then Hom(Λ, -) is a functor from profinitely filtered
pseudo-normed groups equipped with T⁻¹ to itself. Furthermore, if Λ = ℤ then this
functor is isomorphic to the identity functor.

-/

noncomputable theory
universe variables u
open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.

open ProFiltPseuNormGrpWithTinv (of)

def polyhedral_lattice.Hom {r' : ℝ≥0} [fact (0 < r')] (Λ M : Type*) [polyhedral_lattice Λ]
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  ProFiltPseuNormGrpWithTinv r' :=
of r' (Λ →+ M)

namespace PolyhedralLattice
open opposite pseudo_normed_group polyhedral_lattice profinitely_filtered_pseudo_normed_group
open category_theory

variables {r' : ℝ≥0} [fact (0 < r')]

/-- Like `polyhedral_lattice.Hom` but functorial in the first entry.
Unfortunately, this means that the entries are now swapped.
So `(PolyhedralLattice.Hom M).obj (op Λ) = Λ →+ M`. -/
@[simps]
def Hom (M : ProFiltPseuNormGrpWithTinv r') :
  PolyhedralLatticeᵒᵖ ⥤ (ProFiltPseuNormGrpWithTinv r') :=
{ obj := λ Λ, (Hom Λ.unop M),
  map := λ Λ₁ Λ₂ f,
  { to_fun := λ g, g.comp f.unop.to_add_monoid_hom,
    map_zero' := add_monoid_hom.zero_comp _,
    map_add' := λ g₁ g₂, add_monoid_hom.add_comp _ _ _,
    strict' := λ c g hg c' l hl, hg ((f.unop.strict_nnnorm _).trans hl),
    continuous' := λ c,
    begin
      rw [add_monoid_hom.continuous_iff],
      intro l,
      haveI : fact (nnnorm (f.unop l) ≤ nnnorm l) := ⟨f.unop.strict_nnnorm l⟩,
      have aux := (continuous_apply (f.unop l)).comp
        (add_monoid_hom.incl_continuous Λ₁.unop r' M c),
      rwa (embedding_cast_le (c * nnnorm (f.unop l)) (c * nnnorm l)).continuous_iff at aux
    end,
    map_Tinv' := λ g, by { ext l, refl } },
  map_id' := λ Λ, by { ext, refl },
  map_comp' := by { intros, ext, refl } }

end PolyhedralLattice

namespace polyhedral_lattice

/-!
In the remainder of the file, we show that `Hom(ℤ, M)` is isomorphic to `M`.
-/

open pseudo_normed_group profinitely_filtered_pseudo_normed_group_with_Tinv_hom

variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)]
variables (M  : ProFiltPseuNormGrpWithTinv.{u} r')

/-- `HomZ_map` as an equiv. -/
@[simps] def HomZ_map_equiv : Hom ℤ M ≃+ M :=
{ to_fun := add_monoid_hom.eval 1,
  inv_fun := (smul_add_hom ℤ M).flip,
  map_add' := add_monoid_hom.map_add _,
  left_inv := λ f, by { ext, exact one_smul _ _ },
  right_inv := λ x, one_smul _ _ }

lemma HomZ_map_equiv_strict (c : ℝ≥0) (f : (Hom ℤ M)) :
  f ∈ filtration (Hom ℤ M) c ↔ (HomZ_map_equiv M) f ∈ filtration M c :=
begin
  split,
  { intro hf, simpa only [mul_one] using hf int.one_mem_filtration },
  { intros hx c₁ n hn,
    rw [semi_normed_group.mem_filtration_iff] at hn,
    have aux := pseudo_normed_group.int_smul_mem_filtration n _ c hx,
    rw [nnreal.coe_nat_abs] at aux,
    rw [← (HomZ_map_equiv M).symm_apply_apply f, HomZ_map_equiv_symm_apply,
      add_monoid_hom.flip_apply, smul_add_hom_apply, mul_comm],
    exact pseudo_normed_group.filtration_mono (mul_le_mul_right' hn c) aux }
end

lemma HomZ_map_equiv_ctu (c : ℝ≥0) :
  continuous (level (HomZ_map_equiv M) (λ c x , (HomZ_map_equiv_strict M c x).1) c) :=
begin
  haveI : fact (c * nnnorm (1:ℤ) ≤ c) := ⟨by rw [nnnorm_one, mul_one]⟩,
  have aux := add_monoid_hom.incl_continuous ℤ r' M c,
  have aux2 := (continuous_apply 1).comp aux,
  rwa (profinitely_filtered_pseudo_normed_group.embedding_cast_le
    (c * nnnorm (1 : ℤ)) c).continuous_iff at aux2
end

/-- The isomorphism `Hom ℤ M ≅ M` for `M` a `profinitely_filtered_pseudo_normed_group_with_Tinv`. -/
noncomputable
def HomZ_iso : Hom ℤ M ≅ M :=
ProFiltPseuNormGrpWithTinv.iso_of_equiv_of_strict'
  (HomZ_map_equiv M) (HomZ_map_equiv_strict M) (HomZ_map_equiv_ctu M) $
  λ x, by { simp only [add_monoid_hom.eval_apply_apply, HomZ_map_equiv_apply], refl }

end polyhedral_lattice
