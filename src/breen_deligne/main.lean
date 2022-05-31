import breen_deligne.eval2
import for_mathlib.derived.K_projective
import for_mathlib.endomorphisms.Ext
import for_mathlib.endomorphisms.functor

.

noncomputable theory

universes v u

open_locale big_operators

open category_theory category_theory.limits
open bounded_homotopy_category (Ext single)

namespace breen_deligne
namespace package

variables (BD : package)
variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables (F : 𝓐 ⥤ 𝓐) --[preserves_filtered_colimits F]

-- This requires more hypotheses on `BD` and `F`.
-- We'll figure them out while proving the lemma.
-- These extra hypotheses are certainly satisfies by
-- `BD = breen_deligne.package.eg` and
-- `F` = "free condensed abelian group"
-- Also missing: the condition that `A` is torsion free.
lemma main_lemma_bdd (A : 𝓐ᵒᵖ) (B : 𝓐) (j : ℤ) :
  (∀ i ≤ j, is_zero $ ((Ext' i).obj A).obj B) ↔
  (∀ i ≤ j, is_zero $ ((Ext i).obj ((BD.eval F).op.obj A)).obj ((single _ 0).obj B)) :=
sorry

lemma main_lemma_is_zero (A : 𝓐ᵒᵖ) (B : 𝓐) :
  (∀ i, is_zero $ ((Ext' i).obj A).obj B) ↔
  (∀ i, is_zero $ ((Ext i).obj ((BD.eval F).op.obj A)).obj ((single _ 0).obj B)) :=
begin
  split,
  { intros H j,
    refine (main_lemma_bdd BD F A B j).mp _ j le_rfl,
    intros i hij,
    apply H },
  { intros H j,
    refine (main_lemma_bdd BD F A B j).mpr _ j le_rfl,
    intros i hij,
    apply H }
end

section

variables [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐]

def mk_bo_ha_ca_Q (X : 𝓐) (f : X ⟶ X) :
  endomorphisms.mk_bo_ho_ca ((BD.eval F).obj X) ((BD.eval F).map f) ≅
  (BD.eval F.map_endomorphisms).obj ⟨X, f⟩ :=
sorry

lemma main_lemma (A : 𝓐ᵒᵖ) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B) :
  (∀ i, is_iso $ ((Ext' i).map f).app B - ((Ext' i).obj A).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((BD.eval F).op.map f)).app ((single _ 0).obj B) -
    ((Ext i).obj ((BD.eval F).op.obj A)).map ((single _ 0).map g)) :=
begin
  induction A using opposite.rec,
  rw [← f.op_unop, ← endomorphisms.Ext'_is_zero_iff' A B f.unop g, (BD.eval F).op_map, f.op_unop],
  dsimp,
  rw [← endomorphisms.Ext_is_zero_iff'],
  refine (main_lemma_is_zero BD F.map_endomorphisms _ _).trans _,
  apply forall_congr, intro i,
  apply iso.is_zero_iff,
  refine functor.map_iso _ _ ≪≫ iso.app (functor.map_iso _ _) _,
  { exact (endomorphisms.mk_bo_ha_ca_single _ _).symm },
  { refine (mk_bo_ha_ca_Q _ _ _ _).op, },
end

end

end package
end breen_deligne
