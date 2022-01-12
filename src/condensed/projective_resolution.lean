import condensed.ab
import condensed.top_comparison

import for_mathlib.abelian_category
import for_mathlib.ab_epi

universe u

open category_theory

/-

S extr. disc.
A cond ab group.

A ↦ Hom_{CondSet}(S,A) = A(S) commutes with limits and colimits.

A(-) commutes with finite products, in Ab, finite products = finite coproducts.

Z[S] is projective.

A -> B epi, Hom(Z[S],A) -> Hom(Z[S],B) -- A(S) -> B(S) WTS: surjective.

1. If S is extr. disc. and A -> B is an epi of cond ab, then A(S) -> B(S) surjective.
  B -> B/A

-/

noncomputable theory

def Condensed_Ab.free (S : CondensedSet) : Condensed Ab :=
CondensedSet_to_Condensed_Ab.obj $ S

local notation `ℤ[`S`]` := Condensed_Ab.free S.to_Condensed

def Condensed.forget_Ab (S : Condensed Ab) : CondensedSet :=
Condensed_Ab_to_CondensedSet.obj S

def quiver.hom.forget_Ab {S T : Condensed Ab} (e : S ⟶ T) :
  S.forget_Ab ⟶ T.forget_Ab :=
Condensed_Ab_to_CondensedSet.map e

namespace Condensed_Ab

def to_free (S : CondensedSet) : S ⟶ Condensed_Ab_to_CondensedSet.obj (free S) :=
Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _ $ 𝟙 _

def free_lift {S : CondensedSet} {A : Condensed Ab} (e : S ⟶ A.forget_Ab) :
  free S ⟶ A :=
(Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _).symm e

@[simp]
lemma to_free_free_lift {S : CondensedSet} {A : Condensed Ab} (e : S ⟶ A.forget_Ab) :
  to_free S ≫ (free_lift e).forget_Ab = e :=
begin
  dsimp only [Condensed.forget_Ab, to_free, free_lift, quiver.hom.forget_Ab],
  rw [adjunction.hom_equiv_unit, adjunction.hom_equiv_counit, category.assoc,
    category_theory.functor.map_id, category.id_comp, functor.map_comp,
    Condensed_Ab_CondensedSet_adjunction.unit_naturality_assoc,
    adjunction.right_triangle_components, category.comp_id],
end

lemma free_lift_unique {S : CondensedSet} {A : Condensed Ab} (e : S ⟶ A.forget_Ab) (f : free S ⟶ A)
  (h : to_free S ≫ f.forget_Ab = e) : f = free_lift e :=
begin
  apply_fun (Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _),
  dsimp [free_lift],
  rw equiv.apply_symm_apply,
  exact h
end

@[ext]
lemma free_hom_ext {S : CondensedSet} {A : Condensed Ab} (f g : free S ⟶ A)
  (h : to_free S ≫ f.forget_Ab = to_free S ≫ g.forget_Ab) : f = g :=
by rw [free_lift_unique _ f rfl, free_lift_unique _ g rfl, h]

end Condensed_Ab

@[simps]
def hom_equiv_evaluation (S : Profinite.{u}) (A : Condensed Ab) :
  (ℤ[S] ⟶ A) ≃ ((Condensed_Ab_to_CondensedSet ⋙ CondensedSet.evaluation S).obj A) :=
(Condensed_Ab_CondensedSet_adjunction.hom_equiv S.to_Condensed A).trans $
  (equiv_of_fully_faithful $ Sheaf_to_presheaf.{u} _ _).trans $ yoneda'_equiv _ _

local attribute [instance] limits.has_zero_object.has_zero

open category_theory.limits
open opposite

-- sanity check
example (S : Profinite.{u}) : preserves_zero_objects (Condensed.evaluation Ab.{u+1} S) :=
infer_instance

instance (S : Profinite.{u}) [projective S] :
  projective (ℤ[S]) :=
{ factors := λ A B f g hg, begin
    rw epi_iff_is_zero_cokernel at hg,
    -- this follows from the fact that evaluation preserves colimits.
    let e : (cokernel g).val.obj (op S) ≅ cokernel (g.val.app (op S)) := begin
      refine (is_colimit_of_preserves (Condensed.evaluation Ab S)
      (colimit.is_colimit _)).cocone_point_unique_up_to_iso
        (colimit.is_colimit _) ≪≫ has_colimit.iso_of_nat_iso _,
      refine nat_iso.of_components _ _,
      { rintros (a|b), exact eq_to_iso rfl, exact eq_to_iso rfl },
      rintros (a|b) (c|d) (e|e),
      all_goals { dsimp },
      all_goals { simp, try { refl } },
    end,
    replace hg := is_zero_of_preserves (Condensed.evaluation Ab.{u+1} S) hg,
    dsimp [Condensed.evaluation] at hg,
    replace hg := is_zero_of_iso_of_zero hg e,
    rw ← epi_iff_is_zero_cokernel at hg,
    replace hg : function.surjective (g.val.app (op S)) := begin
      resetI,
      apply AddCommGroup.surjective_of_epi,
    end,
    let f₁ := hom_equiv_evaluation _ _ f,
    dsimp at f₁,
    obtain ⟨f',h⟩ := hg f₁,
    use (hom_equiv_evaluation _ _).symm f',
    apply_fun (hom_equiv_evaluation _ _),
    change _ = f₁,
    rw [← h, hom_equiv_evaluation_apply, Sheaf.hom.comp_val, nat_trans.comp_app],
    erw [← comp_apply, ← comp_apply, category.id_comp, ← nat_trans.comp_app, ← nat_trans.comp_app],
    dsimp [hom_equiv_evaluation],
    simp_rw [← category.assoc, ← nat_trans.comp_app],
    rw proetale_topology.to_sheafify_sheafify_lift,
    rw adjunction.hom_equiv_counit,
    dsimp,
    simp only [category.assoc, adjunction.whisker_right_counit_app_app],
    simp_rw [comp_apply],
    congr' 1,
    dsimp [functor.preimage, yoneda'_equiv, full.preimage, AddCommGroup.adj, ulift_functor],
    change (free_abelian_group.lift id) (_ <$> free_abelian_group.of _) = _,
    simp,
  end }
