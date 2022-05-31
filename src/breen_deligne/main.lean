import breen_deligne.eval2
import for_mathlib.derived.K_projective
import for_mathlib.endomorphisms.Ext
import for_mathlib.endomorphisms.functor

.

noncomputable theory

universes v u

open_locale big_operators

open category_theory category_theory.limits opposite
open bounded_homotopy_category (Ext single)

namespace breen_deligne
namespace package

variables (BD : package)
variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables (F : 𝓐 ⥤ 𝓐) --[preserves_filtered_colimits F]

namespace main_lemma

variables (A : 𝓐) (B : 𝓐) (j : ℤ)

def IH  : Prop :=
  (∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B) ↔
  (∀ i ≤ j, is_zero $ ((Ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B))

lemma IH_neg (j : ℤ) (hj : j ≤ 0) (ih : IH BD F A B j) : IH BD F A B (j - 1) :=
begin
  split; intros _ _ hij,
  { apply Ext_single_right_is_zero _ _ 1 _ _ (chain_complex.bounded_by_one _),
    linarith only [hj, hij] },
  { apply Ext'_is_zero_of_neg, linarith only [hj, hij] }
end

lemma IH_0 : IH BD F A B 0 :=
begin
  apply forall_congr, intro i, apply forall_congr, intro hi0,
  rw [le_iff_lt_or_eq] at hi0, rcases hi0 with (hi0|rfl),
  { split; intro,
    { apply Ext_single_right_is_zero _ _ 1 _ _ (chain_complex.bounded_by_one _),
      linarith only [hi0] },
    { apply Ext'_is_zero_of_neg, linarith only [hi0] } },
  apply iso.is_zero_iff,
  -- this can probaby be simplified further,
  -- but ultimately, we need the assumption that `H₀((BD.eval F).obj A)` is isom to `A`
  sorry
end


lemma bdd_step (j : ℤ) (hj : 0 ≤ j) (ih : IH BD F A B j) : IH BD F A B (j + 1) :=
sorry

-- This requires more hypotheses on `BD` and `F`.
-- We'll figure them out while proving the lemma.
-- These extra hypotheses are certainly satisfies by
-- `BD = breen_deligne.package.eg` and
-- `F` = "free condensed abelian group"
-- Also missing: the condition that `A` is torsion free.
lemma bdd (A : 𝓐) (B : 𝓐) (j : ℤ) : IH BD F A B j :=
begin
  apply int.induction_on' j,
  { exact IH_0 BD F A B },
  { exact bdd_step BD F A B },
  { exact IH_neg BD F A B, },
end

lemma is_zero (A : 𝓐) (B : 𝓐) :
  (∀ i, is_zero $ ((Ext' i).obj (op A)).obj B) ↔
  (∀ i, is_zero $ ((Ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B)) :=
begin
  split,
  { intros H j,
    refine (bdd BD F A B j).mp _ j le_rfl,
    intros i hij,
    apply H },
  { intros H j,
    refine (bdd BD F A B j).mpr _ j le_rfl,
    intros i hij,
    apply H }
end

end main_lemma

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
  refine (main_lemma.is_zero BD F.map_endomorphisms _ _).trans _,
  apply forall_congr, intro i,
  apply iso.is_zero_iff,
  refine functor.map_iso _ _ ≪≫ iso.app (functor.map_iso _ _) _,
  { exact (endomorphisms.mk_bo_ha_ca_single _ _).symm },
  { refine (mk_bo_ha_ca_Q _ _ _ _).op, },
end

end

end package
end breen_deligne
