import condensed.ab
import condensed.top_comparison

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

def hom_equiv_evaluation (S : Profinite.{u}) (A : Condensed Ab) :
  (ℤ[S] ⟶ A) ≃ ((Condensed_Ab_to_CondensedSet ⋙ CondensedSet.evaluation S).obj A) :=
(Condensed_Ab_CondensedSet_adjunction.hom_equiv S.to_Condensed A).trans $
  (equiv_of_fully_faithful $ Sheaf_to_presheaf.{u} _ _).trans $ yoneda'_equiv _ _

instance (S : Profinite) [projective S] :
  projective (ℤ[S]) :=
{ factors := λ A B f g hg, begin
    let fS := (Condensed_Ab_to_CondensedSet ⋙ CondensedSet.evaluation S).map g,
    suffices hfS : function.surjective fS,
    { let f' := hom_equiv_evaluation S B f,
      obtain ⟨φ, hφ⟩ := hfS f',
      let φ' := (hom_equiv_evaluation S A).symm φ,
      refine ⟨φ', _⟩,
      apply (hom_equiv_evaluation S B).injective,
      refine eq.trans _ hφ,
      sorry },
    rw ← epi_iff_surjective,
    sorry,
    -- it's a map in `Type`, not in `Ab`, aahrg
    -- apply preadditive.epi_of_cokernel_iso_zero,
  end }
