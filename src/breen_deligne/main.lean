import breen_deligne.eval2
import for_mathlib.derived.K_projective

.

noncomputable theory

open_locale big_operators

open category_theory category_theory.limits
open bounded_homotopy_category (Ext single)

namespace breen_deligne
namespace package

variables (BD : package)
variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜] [enough_projectives 𝒜]
variables (F : 𝒜 ⥤ 𝒜) --[preserves_filtered_colimits F]

-- This requires more hypotheses on `BD` and `F`.
-- We'll figure them out while proving the lemma.
-- These extra hypotheses are certainly satisfies by
-- `BD = breen_deligne.package.eg` and
-- `F` = "free condensed abelian group"
-- Also missing: the condition that `A` is torsion free.
lemma main_lemma_bdd (A : 𝒜ᵒᵖ) (B : 𝒜) (f : A ⟶ A) (g : B ⟶ B) (j : ℤ) :
  (∀ i ≤ j, is_iso $ ((Ext' i).map f).app B - ((Ext' i).obj A).map g) ↔
  (∀ i ≤ j, is_iso $
    ((Ext i).map ((BD.eval F).op.map f)).app ((single _ 0).obj B) -
    ((Ext i).obj ((BD.eval F).op.obj A)).map ((single _ 0).map g)) :=
sorry

lemma main_lemma (A : 𝒜ᵒᵖ) (B : 𝒜) (f : A ⟶ A) (g : B ⟶ B) :
  (∀ i, is_iso $ ((Ext' i).map f).app B - ((Ext' i).obj A).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((BD.eval F).op.map f)).app ((single _ 0).obj B) -
    ((Ext i).obj ((BD.eval F).op.obj A)).map ((single _ 0).map g)) :=
begin
  split,
  { intros H j,
    refine (main_lemma_bdd BD F A B f g j).mp _ j le_rfl,
    intros i hij,
    apply H },
  { intros H j,
    refine (main_lemma_bdd BD F A B f g j).mpr _ j le_rfl,
    intros i hij,
    apply H }
end

end package
end breen_deligne
