import for_mathlib.AddCommGroup.explicit_products

open category_theory
open category_theory.limits

namespace AddCommGroup

universes u
variables {J : Type u} [small_category J] (F : J ⥤ AddCommGroup.{u})

open_locale classical
noncomputable theory

def explicit_cocone_point_kernel :
  add_subgroup (direct_sum J (λ i, F.obj i)) :=
add_subgroup.closure
{ x | ∃ (i j : J) (f : i ⟶ j) (t : F.obj i),
  x = direct_sum.of _ j (F.map f t) - direct_sum.of _ i t  }

def explicit_cocone_point : AddCommGroup.{u} :=
AddCommGroup.of
((direct_sum J (λ i, F.obj i)) ⧸ explicit_cocone_point_kernel F)

def explicit_cocone : cocone F :=
{ X := explicit_cocone_point F,
  ι :=
  { app := λ j, add_monoid_hom.comp (quotient_add_group.mk' _)
      (direct_sum.of _ j),
    naturality' := begin
      intros i j f, ext t,
      simp only [comp_apply, add_monoid_hom.coe_comp,
        quotient_add_group.coe_mk', function.comp_app, functor.const.obj_map,
        id_apply],
      rw quotient_add_group.eq_iff_sub_mem,
      apply add_subgroup.subset_closure,
      dsimp, refine ⟨i, j, f, t, rfl⟩,
    end } }

def is_colimit_explicit_cone : is_colimit (explicit_cocone F) :=
{ desc := λ S, quotient_add_group.lift _
    (direct_sum.to_add_monoid $ λ i, S.ι.app _)
    begin
      intros t ht,
      apply add_subgroup.closure_induction ht,
      { rintros x ⟨i,j,f,t,rfl⟩,
        simp only [map_sub, direct_sum.to_add_monoid_of, cocone.w_apply, sub_self] },
      { simp only [map_zero], },
      { intros x y hx hy, simp only [hx, hy, map_add, add_zero] },
      { intros x hx, simp only [hx, map_neg, neg_zero] },
    end,
  fac' := begin
    intros S j, ext t, dsimp [explicit_cocone],
    simp only [direct_sum.to_add_monoid_of, comp_apply, add_monoid_hom.coe_comp,
      quotient_add_group.coe_mk', quotient_add_group.lift_mk],
  end,
  uniq' := begin
    intros S m hm, ext j t,
    simp only [direct_sum.to_add_monoid_of, add_monoid_hom.coe_comp, quotient_add_group.coe_mk',
      function.comp_app, quotient_add_group.lift_mk],
    rw ← hm, refl,
  end }

end AddCommGroup
