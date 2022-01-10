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

local notation `ℤ[`S`]` := -- might want to make a few more definitions instead of just notation
CondensedSet_to_Condensed_Ab.obj $ S.to_Condensed

noncomputable
def hom_equiv_evaluation (S : Profinite.{u}) (A : Condensed Ab) :
  (ℤ[S] ⟶ A) ≃ ((Condensed_Ab_to_CondensedSet ⋙ CondensedSet.evaluation S).obj A) :=
begin
  refine (Condensed_Ab_CondensedSet_adjunction.hom_equiv S.to_Condensed A).trans _,
  refine (equiv_of_fully_faithful $ Sheaf_to_presheaf.{u} _ _).trans _,
  dsimp,
  -- and now we're stuck because `yoneda_equiv` has quite restrictive universes
  -- refine (@yoneda_equiv _ _ S (A.val ⋙ forget Ab)).trans _,
  sorry
end

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
    -- it's a map in `Type`, not in `Ab`, aahrg
    -- apply preadditive.epi_of_cokernel_iso_zero,
  end }
