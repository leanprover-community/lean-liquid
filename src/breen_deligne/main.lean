import breen_deligne.eval2
import for_mathlib.derived.K_projective
import for_mathlib.endomorphisms.Ext
import for_mathlib.endomorphisms.functor
import for_mathlib.truncation_Ext

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

variables (hH0 : ((BD.eval F).obj A).val.as.homology 0 ≅ A)

include hH0

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

lemma bdd_step₁ (j : ℤ) :
  (∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B) ↔
  (∀ i ≤ j, is_zero $ ((Ext' i).obj (op $ ((BD.eval F).obj A).val.as.homology 0)).obj B) :=
begin
  apply forall_congr, intro i, apply forall_congr, intro hi,
  apply iso.is_zero_iff,
  -- use `hH0` and some `map_iso`
  sorry
end

open bounded_homotopy_category (of')

lemma bdd_step₂ (j : ℤ) :
  (∀ i ≤ j, is_zero $ ((Ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B)) ↔
  (∀ i ≤ j, is_zero $ ((Ext i).obj (op $ of' $ ((BD.eval' F).obj A).truncation 0)).obj ((single _ 0).obj B)) :=
begin
  apply forall_congr, intro i, apply forall_congr, intro hi,
  apply iso.is_zero_iff,
  -- use `cochain_complex.truncation.ι_iso` and some `functor.map_iso`
  sorry
end

omit hH0

lemma bdd_step₃
  (H : ∀ i ≤ j + 1, is_zero (((Ext i).obj (op (of' (((BD.eval' F).obj A).truncation (-1))))).obj ((single 𝓐 0).obj B))) :
  (∀ i ≤ j + 1, is_zero (((Ext i).obj (op (of' (((BD.eval' F).obj A).truncation 0)))).obj ((single 𝓐 0).obj B))) ↔
  ∀ i ≤ j + 1, is_zero (((Ext' i).obj (op (((BD.eval F).obj A).val.as.homology 0))).obj B) :=
-- use `Ext_ι_succ_five_term_exact_seq`
sorry

lemma bdd_step₄
  (H : ∀ t ≤ (-1:ℤ), ∀ i ≤ j, is_zero (((Ext i).obj (op $ (single _ t).obj (((BD.eval F).obj A).val.as.homology t))).obj ((single 𝓐 0).obj B))) :
  ∀ t ≤ (-1:ℤ), ∀ i ≤ j + 1, is_zero (((Ext i).obj (op (of' (((BD.eval' F).obj A).truncation t)))).obj ((single 𝓐 0).obj B)) :=
-- induction on `t` and use `Ext_ι_succ_five_term_exact_seq`
sorry

lemma bdd_step₅ (t i : ℤ) :
  is_zero (((Ext i).obj (op ((single 𝓐 t).obj (((BD.eval F).obj A).val.as.homology t)))).obj ((single 𝓐 0).obj B)) ↔
  is_zero (((Ext' (i+t)).obj (op $ ((BD.eval F).obj A).val.as.homology t)).obj B) :=
begin
  apply iso.is_zero_iff,
  sorry
end

include hH0

lemma bdd_step (j : ℤ) (hj : 0 ≤ j) (ih : IH BD F A B j) : IH BD F A B (j + 1) :=
begin
  by_cases ih' : (∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B), swap,
  { split,
    { intro h, refine (ih' $ λ i hi, _).elim, apply h _ (int.le_add_one hi), },
    { intro h, refine (ih' $ ih.mpr $ λ i hi, _).elim, apply h _ (int.le_add_one hi), } },
  refine (bdd_step₁ BD F _ _ hH0 _).trans ((bdd_step₂ BD F _ _ hH0 _).trans _).symm,
  apply bdd_step₃,
  apply bdd_step₄ BD F A B _ _ _ le_rfl,
  intros t ht i hi,
  rw bdd_step₅,
  sorry
end

-- This requires more hypotheses on `BD` and `F`.
-- We'll figure them out while proving the lemma.
-- These extra hypotheses are certainly satisfies by
-- `BD = breen_deligne.package.eg` and
-- `F` = "free condensed abelian group"
-- Also missing: the condition that `A` is torsion free.
lemma bdd (j : ℤ) : IH BD F A B j :=
begin
  apply int.induction_on' j,
  { exact IH_0 BD F A B hH0 },
  { exact bdd_step BD F A B hH0 },
  { exact IH_neg BD F A B, },
end

lemma is_zero :
  (∀ i, is_zero $ ((Ext' i).obj (op A)).obj B) ↔
  (∀ i, is_zero $ ((Ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B)) :=
begin
  split,
  { intros H j,
    refine (bdd BD F A B hH0 j).mp _ j le_rfl,
    intros i hij,
    apply H },
  { intros H j,
    refine (bdd BD F A B hH0 j).mpr _ j le_rfl,
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

lemma main_lemma (A : 𝓐) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B)
  (hH0 : (((data.eval_functor F).obj BD.data).obj A).homology 0 ≅ A) :
  (∀ i, is_iso $ ((Ext' i).map f.op).app B - ((Ext' i).obj (op A)).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((BD.eval F).map f).op).app ((single _ 0).obj B) -
    ((Ext i).obj (op $ (BD.eval F).obj A)).map ((single _ 0).map g)) :=
begin
  rw [← endomorphisms.Ext'_is_zero_iff' A B f g],
  rw [← endomorphisms.Ext_is_zero_iff'],
  refine (main_lemma.is_zero BD F.map_endomorphisms _ _ _).trans _,
  { sorry },
  apply forall_congr, intro i,
  apply iso.is_zero_iff,
  refine functor.map_iso _ _ ≪≫ iso.app (functor.map_iso _ _) _,
  { exact (endomorphisms.mk_bo_ha_ca_single _ _).symm },
  { refine (mk_bo_ha_ca_Q _ _ _ _).op, },
end

end

end package
end breen_deligne
