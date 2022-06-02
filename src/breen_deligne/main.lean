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

lemma IH_0_aux (C : bounded_homotopy_category 𝓐) (hC : C.val.bounded_by 1) :
  ((Ext' 0).flip.obj B).obj (op (C.val.as.homology 0)) ≅
  ((Ext 0).obj (op C)).obj ((single 𝓐 0).obj B) :=
sorry

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
  refine ((Ext' 0).flip.obj B).map_iso hH0.op ≪≫ _,
  apply IH_0_aux,
  apply chain_complex.bounded_by_one,
end

lemma bdd_step₁ (j : ℤ) :
  (∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B) ↔
  (∀ i ≤ j, is_zero $ ((Ext' i).obj (op $ ((BD.eval F).obj A).val.as.homology 0)).obj B) :=
begin
  apply forall_congr, intro i, apply forall_congr, intro hi,
  apply iso.is_zero_iff,
  exact ((Ext' _).flip.obj B).map_iso hH0.op,
end

open bounded_homotopy_category (of' Ext_map_is_iso_of_quasi_iso)

lemma bdd_step₂ (j : ℤ) :
  (∀ i ≤ j, is_zero $ ((Ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B)) ↔
  (∀ i ≤ j, is_zero $ ((Ext i).obj (op $ of' $ ((BD.eval' F).obj A).truncation 0)).obj ((single _ 0).obj B)) :=
begin
  apply forall_congr, intro i, apply forall_congr, intro hi,
  apply iso.is_zero_iff,
  refine ((Ext _).flip.obj ((single _ 0).obj B)).map_iso _,
  refine iso.op _,
  haveI := cochain_complex.truncation.ι_iso ((BD.eval' F).obj A) 0 _,
  swap, { apply chain_complex.bounded_by_one },
  let e' := (as_iso $ cochain_complex.truncation.ι ((BD.eval' F).obj A) 0),
  let e := (homotopy_category.quotient _ _).map_iso e',
  refine ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩,
end

omit hH0

lemma bdd_step₃_aux (i j : ℤ) :
  is_zero (((Ext i).obj (op $ (single 𝓐 j).obj (((BD.eval F).obj A).val.as.homology j))).obj ((single 𝓐 0).obj B)) ↔
  is_zero (((Ext i).obj (op $ of' (((BD.eval' F).obj A).imker j))).obj ((single 𝓐 0).obj B)) :=
begin
  apply iso.is_zero_iff,
  let φ : (single 𝓐 j).obj (((BD.eval F).obj A).val.as.homology j) ⟶ of' (((BD.eval' F).obj A).imker j) :=
    (homotopy_category.quotient _ _).map (cochain_complex.imker.to_single ((BD.eval' F).obj A) _),
  haveI : homotopy_category.is_quasi_iso φ :=
    cochain_complex.imker.to_single_quasi_iso ((BD.eval' F).obj A) _,
  let e := @as_iso _ _ _ _ _ (Ext_map_is_iso_of_quasi_iso _ _ ((single 𝓐 0).obj B) φ i),
  exact e,
end

lemma bdd_step₃
  (H : ∀ i ≤ j + 1, is_zero (((Ext i).obj (op (of' (((BD.eval' F).obj A).truncation (-1))))).obj ((single 𝓐 0).obj B))) :
  (∀ i ≤ j + 1, is_zero (((Ext i).obj (op (of' (((BD.eval' F).obj A).truncation 0)))).obj ((single 𝓐 0).obj B))) ↔
  ∀ i ≤ j + 1, is_zero (((Ext' i).obj (op (((BD.eval F).obj A).val.as.homology 0))).obj B) :=
begin
  apply forall_congr, intro i, apply forall_congr, intro hi,
  refine iff.trans _ (bdd_step₃_aux BD F A B i 0).symm,
  obtain ⟨i, rfl⟩ : ∃ k, k+1 = i := ⟨i-1, sub_add_cancel _ _⟩,
  have LES1 := cochain_complex.Ext_ι_succ_five_term_exact_seq ((BD.eval' F).obj A) ((single 𝓐 0).obj B) (-1) i,
  have LES2 := cochain_complex.Ext_ι_succ_five_term_exact_seq ((BD.eval' F).obj A) ((single 𝓐 0).obj B) (-1) (i+1),
  have aux := ((LES1.drop 2).pair.cons LES2).is_iso_of_zero_of_zero; clear LES1 LES2,
  refine (@as_iso _ _ _ _ _ (aux _ _)).is_zero_iff; clear aux,
  { apply (H _ _).eq_of_src, exact (int.le_add_one le_rfl).trans hi },
  { apply (H _ hi).eq_of_tgt, },
end

lemma bdd_step₄
  (H : ∀ t ≤ (-1:ℤ), ∀ i ≤ j, is_zero (((Ext i).obj (op $ (single _ t).obj (((BD.eval F).obj A).val.as.homology t))).obj ((single 𝓐 0).obj B))) :
  ∀ t ≤ (-1:ℤ), ∀ i ≤ j + 1, is_zero (((Ext i).obj (op (of' (((BD.eval' F).obj A).truncation t)))).obj ((single 𝓐 0).obj B)) :=
begin
  intros t ht i, revert ht,
  apply int.induction_on' t (-i-1),
  { intros hi1 hi2,
    apply Ext_single_right_is_zero _ _ (-i-1+1),
    { apply cochain_complex.truncation.bounded_by },
    { simp only [sub_add_cancel, add_left_neg], } },
  -- induction on `t` and use `Ext_ι_succ_five_term_exact_seq`
  sorry,
  sorry
end

lemma bdd_step₅ (t i : ℤ) :
  is_zero (((Ext i).obj (op ((single 𝓐 t).obj (((BD.eval F).obj A).val.as.homology t)))).obj ((single 𝓐 0).obj B)) ↔
  is_zero (((Ext' (i+t)).obj (op $ ((BD.eval F).obj A).val.as.homology t)).obj B) :=
begin
  apply iso.is_zero_iff,
  -- this should follow from the defn of `Ext`
  sorry
end

-- `T` is a tensor product functor
variables (T : 𝓐 ⥤ Ab ⥤ 𝓐)

-- this needs extra assumptions:
-- * `T.obj A` should map a free resolution `0 → F₁ → F₂ → A' → 0` to a short exact sequence
-- * `T.obj A` should map a free object `F = ℤ^κ` to `A^κ`
lemma bdd_step₆ (IH : ∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B)
  (i : ℤ) (hi : i ≤ j) (A' : Ab) :
  is_zero (((Ext' i).flip.obj B).obj (op ((T.obj A).obj A'))) :=
sorry

variables (hAT : ∀ t ≤ (-1:ℤ), ∃ A', nonempty ((T.obj A).obj A' ≅ ((BD.eval F).obj A).val.as.homology t))

include hH0 hAT

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
  obtain ⟨A', ⟨e⟩⟩ := hAT t ht,
  apply (((Ext' (i+t)).flip.obj B).map_iso e.op).is_zero_iff.mpr,
  apply bdd_step₆ A B _ T ih',
  linarith only [ht, hi]
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
  { exact bdd_step BD F A B hH0 T hAT },
  { exact IH_neg BD F A B, },
end

lemma is_zero :
  (∀ i, is_zero $ ((Ext' i).obj (op A)).obj B) ↔
  (∀ i, is_zero $ ((Ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B)) :=
begin
  split,
  { intros H j,
    refine (bdd BD F A B hH0 T hAT j).mp _ j le_rfl,
    intros i hij,
    apply H },
  { intros H j,
    refine (bdd BD F A B hH0 T hAT j).mpr _ j le_rfl,
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
  refine (main_lemma.is_zero BD F.map_endomorphisms _ _ _ _ _).trans _,
  { sorry },
  -- the next `sorry` are not provable in general,
  -- they should be made assumptions that can be filled in when applied to `Cond(Ab)`
  { sorry },
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
