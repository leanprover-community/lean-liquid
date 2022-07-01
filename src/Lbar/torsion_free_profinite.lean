import algebra.category.Group.limits
import for_mathlib.Profinite.extend
import Lbar.basic
import Lbar.functor
import pseudo_normed_group.category.strictProFiltPseuNormGrpWithTinv
import pseudo_normed_group.bounded_limits

noncomputable theory

universes u v

open_locale nnreal


set_option pp.universes true

open Lbar Profinite CommGroup category_theory.limits

lemma limit_torsion_free_to_Ab
  (C : Type u) [category_theory.small_category C] (J : C ⥤ Ab.{u})
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (limit J).α :=
begin
  let L := get_limit_cone _,
  haveI := AddCommGroup.forget_preserves_limits.{u u},
  have h_inj := @concrete.to_product_injective_of_is_limit AddCommGroup.{u} _ _
    C _ J _ L.cone L.is_limit,
  fconstructor,
  intros c x hx,
  let φ := λ x : (limit J), λ j, (L.cone.π.app j) x,
  have h1: φ 0 = 0,
  { ext j,
    exact (L.cone.π.app j).2 },
  have h2: φ (c • x) = c • φ x,
  { ext j,
    exact map_zsmul (L.cone.π.app j) _ _ },
  apply_fun φ at hx,
  simp only [h1, h2, pi.zero_def, function.funext_iff, pi.smul_apply, smul_eq_zero] at hx,
  by_cases hc : c = 0,
  { apply or.intro_left, exact hc},
  { simp only [hc, false_or] at hx,
    apply or.intro_right,
    apply h_inj,
    funext j,
    specialize hx j,
    simp only [_root_.map_zero],
    exact hx },
end

--[FAE] not needed for LTE, may be for mathlib?
lemma add_comm_group.limit_on_nat_torsion_free
  (J : (category_theory.as_small.{u} ℕ) ⥤ AddCommGroup.{u})
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (limit J).α := limit_torsion_free_to_Ab (category_theory.as_small.{u} ℕ) J h_tf


--[FAE] The following might be useless because the instance on line 89 might be false
-- lemma limit_torsion_free_to_PFPNGwithTinv {C : Type u} [category_theory.small_category C]
--   (J : C ⥤ (ProFiltPseuNormGrpWithTinv₁.{u} r'))
--   [preserves_limit J
--     (category_theory.forget.{u+1 u u}(ProFiltPseuNormGrpWithTinv₁.{u} r'))]
--   (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
--   : no_zero_smul_divisors ℤ (limit J).M :=
-- begin
--   let L := get_limit_cone _,
--   have h_inj := @concrete.to_product_injective_of_is_limit (ProFiltPseuNormGrpWithTinv₁.{u} r') _ _ C _ J _ L.cone L.is_limit,
--   fconstructor,
--   intros c x hx,
--   let φ := λ x : limit J, λ j, (L.cone.π.app j) x,
--   have h1: φ 0 = 0,
--   { ext j,
--     exact (L.cone.π.app j).2 },
--   have h2: φ (c • x) = c • φ x,
--   { ext j,
--     apply comphaus_filtered_pseudo_normed_group_with_Tinv_hom.map_zsmul },
--   apply_fun φ at hx,
--   simp only [h1, h2, pi.zero_def, function.funext_iff, pi.smul_apply, smul_eq_zero] at hx,
--   by_cases hc : c = 0,
--   { apply or.intro_left, exact hc},
--   { simp only [hc, false_or] at hx,
--     apply or.intro_right,
--     apply h_inj,
--     funext j,
--     specialize hx j,
--     simp only [comphaus_filtered_pseudo_normed_group_with_Tinv_hom.map_zero],
--     exact hx },
-- end

-- instance (S : Profinite.{u}) : preserves_limit (fintype_diagram S ⋙ Fintype_Lbar.{u u} r') (category_theory.forget.{u+1 u u}(ProFiltPseuNormGrpWithTinv₁.{u} r')) := sorry

-- instance (S : Profinite.{u}) : no_zero_smul_divisors ℤ ((extend (Fintype_Lbar.{u u} r')).obj S) :=
-- begin
--   apply limit_torsion_free_to_PFPNGwithTinv (fintype_diagram S ⋙ Fintype_Lbar.{u u} r'),
--   intro _,
--   exact Fintype.Lbar_no_zero_smul_divisors.{u} _ r',
-- end

section bounded

-- open profinitely_filtered_pseudo_normed_group_with_Tinv

-- variables (C : Type u) [category_theory.small_category C]
-- variable (S : Profinite.{u})

variables (r' : ℝ≥0) [fact (0 < r')]

-- variable (J : C ⥤ (ProFiltPseuNormGrpWithTinv₁.{u} r'))
-- variable (J : (discrete_quotient.{u} S) ⥤ (ProFiltPseuNormGrpWithTinv.{u} r'))

def to_Ab : (ProFiltPseuNormGrpWithTinv₁.{u} r') ⥤ Ab.{u} :=
{ obj := λ M, AddCommGroup.of M,
  map := λ M N f, f.to_add_monoid_hom }

def to_PseuNormGrp₁ : (ProFiltPseuNormGrpWithTinv₁.{u} r') ⥤ PseuNormGrp₁.{u} :=
PFPNGT₁_to_CHFPNG₁ₑₗ _ ⋙ CompHausFiltPseuNormGrp₁.to_PNG₁
/-
{ obj := λ X,
  { carrier := X.1,
  str := sorry,
  exhaustive' := sorry },
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry }
-/

-- variable (L : limit_cone.{u} (J ⋙ (to_Ab r')))
-- variable (L' : limit_cone.{u} (J ⋙ (to_PseuNormGrp₁.{u} r') ⋙ (PseuNormGrp₁.to_Ab)))


-- def bounded_cone_point : (ProFiltPseuNormGrpWithTinv₁.{u} r') := sorry

-- { x | ∃ c, ∀ j, C.cone.π.app j x ∈ pseudo_normed_group.filtration (K.obj j) c },
-- variable (X : C)
-- variable (c : ℝ≥0)
-- -- variable (a)
-- #check pseudo_normed_group.filtration (J.obj X) c
-- variable (y : L.cone.1)
-- #check L.cone.π.app X y ∈ (pseudo_normed_group.filtration (J.obj X) c)

-- #check {y : L.cone.1 | ∃ c, ∀ X, L.cone.π.app X y ∈ (pseudo_normed_group.filtration (J.obj X) c)}



-- def bounded_cone : cone.{u} J :=
-- { X :=
--   { M := @PseuNormGrp₁.bounded_elements.{u} C _ (J ⋙ (to_PseuNormGrp₁.{u} r')) L',
--   str := sorry,
--   exhaustive' := sorry },
--   π := sorry }

-- #check bounded_cone.{u} C _ J
-- #check (@PseuNormGrp₁.bounded_cone.{u} C _ (J ⋙ (to_PseuNormGrp₁.{u} r')) L').1

-- def bounded_cone_is_limit : is_limit (bounded_cone.{u} C r' J) := sorry

instance preserves_limits : preserves_limits (to_PseuNormGrp₁ r') :=
category_theory.limits.comp_preserves_limits _ _

instance (S : Profinite.{u}) : no_zero_smul_divisors ℤ ((extend (Fintype_Lbar.{u u} r')).obj S) :=
begin
  /-
  AT: Here is the skeleton I would recommend.

  -- START
  let T := Ab.explicit_limit_cone.{u u} ((S.fintype_diagram ⋙ Fintype_Lbar.{u u} r' ⋙
    to_PseuNormGrp₁ _) ⋙ PseuNormGrp₁.to_Ab),
  let hT : is_limit T := Ab.explicit_limit_cone_is_limit _,
  let E := PseuNormGrp₁.bounded_cone ⟨T,hT⟩,
  let hE : is_limit E := PseuNormGrp₁.bounded_cone_is_limit _,
  suffices claim : no_zero_smul_divisors ℤ E.X,
  { resetI,
    let iso : (to_PseuNormGrp₁ _).obj ((extend (Fintype_Lbar.{u u} r')).obj S) ≅ E.X :=
      (is_limit_of_preserves (to_PseuNormGrp₁ _)
      (limit.is_limit _)).cone_point_unique_up_to_iso hE,
    have : function.injective iso.hom, sorry,
    apply function.injective.no_zero_smul_divisors iso.hom this,
    any_goals { apply_instance },
    { sorry },
    { sorry } },
  let ι : E.X →+ T.X := add_subgroup.subtype _,
  apply function.injective.no_zero_smul_divisors ι (subtype.val_injective.{u+1}) ι.map_zero,
  any_goals { apply_instance },
  { intros c x, apply ι.map_zsmul, },
  sorry,
  --At this point, we have to show that the point of the explicit limit cone of plain
  --abelian groups is torsion-free. This should already be defeq to a subtype of the product!
  --The finite case should then give us the result.
  --END
  -/

  -- have bdd_L := bounded_cone.{u} (discrete_quotient.{u} ↥S) r'
  --   (fintype_diagram.{u} S ⋙ (Fintype_Lbar.{u u} r')),
  have lim_to_Ab : limit_cone.{u u u u+1}
    ((S.fintype_diagram ⋙ Fintype_Lbar.{u u} r' ⋙ to_PseuNormGrp₁.{u} r')
      ⋙ PseuNormGrp₁.to_Ab.{u}), sorry,--combine extend with the fact that
        -- PFPNG_withTinv ≫ PNG₁ creates limits
  have bdd_L := @PseuNormGrp₁.bounded_cone.{u} (discrete_quotient.{u} ↥S) _
    (fintype_diagram.{u} S ⋙ (Fintype_Lbar.{u u} r' ⋙ (to_PseuNormGrp₁.{u} r'))) lim_to_Ab,
  have h_tf : no_zero_smul_divisors ℤ bdd_L.1, sorry,--this is `lemma limit_torsion_free_to_Ab` above
  have iso : ((extend (Fintype_Lbar.{u u} r')).obj S).1 ≃ₗ[ℤ] bdd_L.1, sorry,--uniqueness of limits
  refine @function.injective.no_zero_smul_divisors ℤ _ _ _ _ _ _ _ h_tf iso.1
   iso.injective iso.map_zero (linear_equiv.map_smul _),
end

end bounded
