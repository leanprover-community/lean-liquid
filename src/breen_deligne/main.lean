import breen_deligne.eval2
import breen_deligne.apply_Pow
import for_mathlib.derived.K_projective
import for_mathlib.endomorphisms.Ext
import for_mathlib.endomorphisms.functor
import for_mathlib.truncation_Ext
import for_mathlib.single_coproducts
import category_theory.limits.opposites
import for_mathlib.free_abelian_group2
import for_mathlib.has_homology_aux
import for_mathlib.exact_functor

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

def IH_0_aux (C : bounded_homotopy_category 𝓐) (hC : C.val.bounded_by 1) :
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
  let φ : of' (((BD.eval' F).obj A).imker j) ⟶ (single 𝓐 j).obj (((BD.eval F).obj A).val.as.homology j) :=
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
  symmetry,
  refine (@as_iso _ _ _ _ _ (aux _ _)).is_zero_iff; clear aux,
  { apply (H _ _).eq_of_src, exact (int.le_add_one le_rfl).trans hi },
  { apply (H _ hi).eq_of_tgt, },
end

lemma bdd_step₄
  (H : ∀ t ≤ (-1:ℤ), ∀ i ≤ j + 1, is_zero (((Ext i).obj (op $ (single _ t).obj (((BD.eval F).obj A).val.as.homology t))).obj ((single 𝓐 0).obj B))) :
  ∀ t ≤ (-1:ℤ), ∀ i ≤ j + 1, is_zero (((Ext i).obj (op (of' (((BD.eval' F).obj A).truncation t)))).obj ((single 𝓐 0).obj B)) :=
begin
  intros t ht i, revert ht,
  apply int.induction_on' t (-i-1),
  { intros hi1 hi2,
    apply Ext_single_right_is_zero _ _ (-i-1+1),
    { apply cochain_complex.truncation.bounded_by },
    { simp only [sub_add_cancel, add_left_neg], } },
  { intros k hk ih hk' hij,
    have LES := cochain_complex.Ext_ι_succ_five_term_exact_seq ((BD.eval' F).obj A) ((single 𝓐 0).obj B) k i,
    apply LES.pair.is_zero_of_is_zero_is_zero; clear LES,
    { erw ← bdd_step₃_aux,
      apply H _ hk' _ hij, },
    { exact ih ((int.le_add_one le_rfl).trans hk') hij, }, },
  { intros k hk ih hk' hij,
    apply Ext_single_right_is_zero _ _ (k-1+1),
    { apply cochain_complex.truncation.bounded_by },
    { linarith only [hk, hk', hij] } },
end

open bounded_homotopy_category (Ext0)

-- move me
def bdd_step₅_aux'' (X Y : bounded_homotopy_category 𝓐)
  (e : bounded_homotopy_category 𝓐 ≌ bounded_homotopy_category 𝓐)
  [e.functor.additive] :
  (preadditive_yoneda.obj X).obj (op Y) ≅
    (preadditive_yoneda.obj (e.functor.obj X)).obj (op (e.functor.obj Y)) :=
add_equiv.to_AddCommGroup_iso $
{ map_add' := λ f g, e.functor.map_add,
  .. equiv_of_fully_faithful e.functor }

instance shift_equiv_functor_additive (k : ℤ) :
  (shift_equiv (bounded_homotopy_category 𝓐) k).functor.additive :=
bounded_homotopy_category.shift_functor_additive k

def bdd_step₅_aux' (X Y : bounded_homotopy_category 𝓐) (k : ℤ) :
  (preadditive_yoneda.obj X).obj (op Y) ≅ (preadditive_yoneda.obj (X⟦k⟧)).obj (op (Y⟦k⟧)) :=
bdd_step₅_aux'' _ _ $ shift_equiv _ k

def bdd_step₅_aux (X Y : bounded_homotopy_category 𝓐) (k : ℤ) :
  (Ext0.obj (op X)).obj Y ≅ (Ext0.obj (op $ X⟦k⟧)).obj (Y⟦k⟧) :=
begin
  delta Ext0, dsimp only,
  refine bdd_step₅_aux' _ _ k ≪≫
    (preadditive_yoneda.obj ((shift_functor (bounded_homotopy_category 𝓐) k).obj Y)).map_iso _,
  refine iso.op _,
  exact bounded_homotopy_category.replacement_iso _ _ (X⟦k⟧) (X⟦k⟧).π (X.π⟦k⟧'),
end

lemma bdd_step₅ (k i : ℤ) :
  is_zero (((Ext i).obj (op ((single 𝓐 k).obj A))).obj ((single 𝓐 0).obj B)) ↔
  is_zero (((Ext' (i+k)).obj (op $ A)).obj B) :=
begin
  apply iso.is_zero_iff,
  dsimp only [Ext', Ext, functor.comp_obj, functor.flip_obj_obj, whiskering_left_obj_obj],
  refine bdd_step₅_aux _ _ k ≪≫ _,
  refine functor.map_iso _ _ ≪≫ iso.app (functor.map_iso _ _) _,
  { refine (shift_add _ _ _).symm },
  { refine ((bounded_homotopy_category.shift_single_iso k k).app A).op.symm ≪≫ _,
    refine eq_to_iso _, rw sub_self, refl },
end

-- `T` should be thought of as a tensor product functor,
-- taking tensor products with `A : Condensed Ab`
variables (T : Ab.{v} ⥤ 𝓐)
variables [∀ α : Type v, preserves_colimits_of_shape (discrete α) T]
variables (hT1 : T.obj (AddCommGroup.of $ punit →₀ ℤ) ≅ A)
variables (hT : ∀ {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z), short_exact f g → short_exact (T.map f) (T.map g))

lemma bdd_step₆_free₀ (A : Ab) :
  ∃ (F₁ F₀ : Ab) (h₁ : module.free ℤ F₁) (h₀ : module.free ℤ F₀) (f : F₁ ⟶ F₀) (g : F₀ ⟶ A),
  short_exact f g :=
begin
  let g := finsupp.total A A ℤ id,
  let F := g.ker,
  let f := F.subtype,
  let F₀ : Ab := AddCommGroup.of (↥A →₀ ℤ),
  let F₁ : Ab := AddCommGroup.of F,
  refine ⟨F₁, F₀, _, _, f.to_add_monoid_hom, g.to_add_monoid_hom, _⟩,
  { dsimp [F₁, F],
    exact submodule.free_of_pid_of_free, },
  { exact module.free.finsupp.free ℤ },
  { apply_with short_exact.mk {instances:=ff},
    { rw AddCommGroup.mono_iff_injective, apply subtype.val_injective },
    { rw AddCommGroup.epi_iff_surjective, apply finsupp.total_id_surjective },
    { rw AddCommGroup.exact_iff,
      ext x,
      dsimp only [f, F, F₁, AddCommGroup.coe_of],
      simp only [add_monoid_hom.mem_range, linear_map.to_add_monoid_hom_coe,
        submodule.subtype_apply],
      refine ⟨_, _⟩,
      { rintro ⟨y, rfl⟩, exact y.2 },
      { intro h, exact ⟨⟨x, h⟩, rfl⟩ } } }
end

include hT1

variables [has_coproducts 𝓐] [AB4 𝓐]

lemma bdd_step₆_free₁
  (IH : ∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B)
  (i : ℤ) (hi : i ≤ j) (α : Type v) :
  is_zero (((Ext' i).flip.obj B).obj (op (T.obj $ AddCommGroup.of $ α →₀ ℤ))) :=
begin
  let D : discrete α ⥤ Ab := discrete.functor (λ a, AddCommGroup.of $ punit →₀ ℤ),
  let c : cocone D := cofan.mk (AddCommGroup.of $ α →₀ ℤ)
    (λ a, finsupp.map_domain.add_monoid_hom $ λ _, a),
  let hc : is_colimit c := ⟨λ s, _, _, _⟩,
  rotate,
  { refine (finsupp.total _ _ _ (λ a, _)).to_add_monoid_hom,
    refine (s.ι.app a) (finsupp.single punit.star 1) },
  { intros s a, apply finsupp.add_hom_ext', rintro ⟨⟩, apply add_monoid_hom.ext_int,
    simp only [add_monoid_hom.comp_apply, category_theory.comp_apply,
      linear_map.to_add_monoid_hom_coe, cofan.mk_ι_app,
      finsupp.map_domain.add_monoid_hom_apply, finsupp.map_domain_single,
      finsupp.single_add_hom_apply, finsupp.total_single, one_smul], },
  { intros s m h,
    apply finsupp.add_hom_ext', intro a, apply add_monoid_hom.ext_int,
    simp only [add_monoid_hom.comp_apply, linear_map.to_add_monoid_hom_coe,
      finsupp.single_add_hom_apply, finsupp.total_single, one_smul],
    rw ← h,
    simp only [category_theory.comp_apply, cofan.mk_ι_app,
      finsupp.map_domain.add_monoid_hom_apply, finsupp.map_domain_single], },
  let c' := T.map_cocone c,
  let hc' : is_colimit c' := is_colimit_of_preserves T hc,
  let c'' := ((Ext' i).flip.obj B).right_op.map_cocone c',
  let hc'' : is_colimit c'' := is_colimit_of_preserves _ hc',
  change is_zero c''.X.unop,
  apply is_zero.unop,
  haveI : has_colimits Ab.{v}ᵒᵖ := has_colimits_op_of_has_limits.{v v+1},
  let e : c''.X ≅ colimit ((D ⋙ T) ⋙ ((Ext' i).flip.obj B).right_op) :=
    hc''.cocone_point_unique_up_to_iso (colimit.is_colimit _),
  apply is_zero.of_iso _ e,
  apply is_zero_colimit,
  intros j,
  apply is_zero.of_iso _ (((Ext' i).flip.obj B).right_op.map_iso hT1),
  apply (IH i hi).op,
end

lemma bdd_step₆_free
  (IH : ∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B)
  (i : ℤ) (hi : i ≤ j) (A' : Ab) (hA' : module.free ℤ A') :
  is_zero (((Ext' i).flip.obj B).obj (op (T.obj A'))) :=
begin
  let e' := module.free.choose_basis ℤ A',
  let e'' := e'.repr.to_add_equiv,
  let e : A' ≅ (AddCommGroup.of $ module.free.choose_basis_index ℤ A' →₀ ℤ),
  { refine add_equiv_iso_AddCommGroup_iso.hom _, exact e'' },
  refine is_zero.of_iso _ (functor.map_iso _ (T.map_iso e).op.symm),
  apply bdd_step₆_free₁ A B j T hT1 IH i hi,
end

include hT

lemma bdd_step₆
  (IH : ∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B)
  (i : ℤ) (hi : i ≤ j) (A' : Ab) :
  is_zero (((Ext' i).flip.obj B).obj (op (T.obj A'))) :=
begin
  obtain ⟨F₁, F₀, h₁, h₀, f, g, hfg⟩ := bdd_step₆_free₀ A',
  specialize hT f g hfg,
  obtain ⟨i, rfl⟩ : ∃ k, k+1=i := ⟨i-1, sub_add_cancel _ _⟩,
  have := ((hT.Ext'_five_term_exact_seq B i).drop 2).pair,
  apply this.is_zero_of_is_zero_is_zero,
  { apply bdd_step₆_free A B j T hT1 IH _ ((int.le_add_one le_rfl).trans hi) _ h₁, },
  { apply bdd_step₆_free A B j T hT1 IH _ hi _ h₀, },
end

variables (hAT : ∀ t ≤ (-1:ℤ), ∃ A', nonempty (T.obj A' ≅ ((BD.eval F).obj A).val.as.homology t))

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
  apply bdd_step₆ A B _ T hT1 @hT ih',
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
  { exact bdd_step BD F A B hH0 T hT1 @hT hAT },
  { exact IH_neg BD F A B, },
end

lemma is_zero :
  (∀ i, is_zero $ ((Ext' i).obj (op A)).obj B) ↔
  (∀ i, is_zero $ ((Ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B)) :=
begin
  split,
  { intros H j,
    refine (bdd BD F A B hH0 T hT1 @hT hAT j).mp _ j le_rfl,
    intros i hij,
    apply H },
  { intros H j,
    refine (bdd BD F A B hH0 T hT1 @hT hAT j).mpr _ j le_rfl,
    intros i hij,
    apply H }
end

end main_lemma

section

variables [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐]
variables [has_products_of_shape (ulift.{v} ℕ) 𝓐]

open category_theory.preadditive

@[simps, nolint unused_arguments]
def Pow_X (X : endomorphisms 𝓐) (n : ℕ) :
  ((Pow n).obj X).X ≅ (Pow n).obj X.X :=
(apply_Pow (endomorphisms.forget 𝓐) n).app X
.

instance eval'_bounded_above (X : 𝓐) : ((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj ((BD.eval' F).obj X)).is_bounded_above :=
((BD.eval F).obj X).bdd

def mk_bo_ha_ca'_Q (X : 𝓐) (f : X ⟶ X) :
  endomorphisms.mk_bo_ho_ca' ((BD.eval' F).obj X) ((BD.eval' F).map f) ≅
  (BD.eval F.map_endomorphisms).obj ⟨X, f⟩ :=
bounded_homotopy_category.mk_iso $ (homotopy_category.quotient _ _).map_iso
begin
  refine homological_complex.hom.iso_of_components _ _,
  { intro i,
    refine endomorphisms.mk_iso _ _,
    { rcases i with ((_|i)|i),
      { refine F.map_iso _, symmetry, refine (Pow_X _ _) },
      { refine (is_zero_zero _).iso _, apply endomorphisms.is_zero_X, exact is_zero_zero _ },
      { refine F.map_iso _, symmetry, refine (Pow_X _ _) } },
    { rcases i with ((_|i)|i),
      { show F.map _ ≫ F.map _ = F.map _ ≫ F.map _,
        rw [← F.map_comp, ← F.map_comp], congr' 1,
        apply biproduct.hom_ext', intro j,
        dsimp only [Pow, Pow_X_hom, Pow_X_inv, iso.symm_hom],
        rw [biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc, ← endomorphisms.hom.comm], },
      { apply is_zero.eq_of_tgt, apply endomorphisms.is_zero_X, exact is_zero_zero _ },
      { show F.map _ ≫ F.map _ = F.map _ ≫ F.map _,
        rw [← F.map_comp, ← F.map_comp], congr' 1,
        apply biproduct.hom_ext', intro j,
        dsimp only [Pow, Pow_X_hom, Pow_X_inv, iso.symm_hom],
        rw [biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc, ← endomorphisms.hom.comm], } } },
  { rintro i j (rfl : _ = _), ext, rcases i with (i|(_|i)),
    { apply is_zero.eq_of_tgt, apply endomorphisms.is_zero_X, exact is_zero_zero _ },
    { change F.map _ ≫ _ = _ ≫ F.map _,
      dsimp only, erw [eval'_obj_d_0 _ _ _ 0, eval'_obj_d_0 _ _ _ 0],
      simp only [universal_map.eval_Pow, free_abelian_group.lift_eq_sum, ← endomorphisms.forget_map,
        sum_comp, comp_sum, nat_trans.app_sum, functor.map_sum, whisker_right_app,
        zsmul_comp, comp_zsmul, nat_trans.app_zsmul, functor.map_zsmul],
      refine finset.sum_congr rfl _, intros g hg, refine congr_arg2 _ rfl _,
      dsimp only [endomorphisms.forget_map, functor.map_endomorphisms_map_f],
      rw [← functor.map_comp, ← functor.map_comp], congr' 1,
      dsimp only [basic_universal_map.eval_Pow_app, iso.symm_hom, Pow_X_inv],
      ext j : 2,
      rw [biproduct.ι_desc_assoc, biproduct.ι_matrix_assoc, ← endomorphisms.comp_f,
        biproduct.ι_matrix, biproduct.lift_desc],
      have := (endomorphisms.forget _).map_id ⟨X,f⟩, dsimp only [endomorphisms.forget_obj] at this,
      simp only [← endomorphisms.forget_map, ← this, ← functor.map_zsmul, ← functor.map_sum, ← functor.map_comp],
      congr' 1,
      apply biproduct.hom_ext, intro i,
      simp only [biproduct.lift_π, sum_comp, category.assoc],
      rw finset.sum_eq_single_of_mem i (finset.mem_univ _),
      { rw [biproduct.ι_π, dif_pos rfl, eq_to_hom_refl, category.comp_id], },
      { rintro k - hk, rw [biproduct.ι_π_ne _ hk, comp_zero], } },
    { change F.map _ ≫ _ = _ ≫ F.map _,
      dsimp only, erw [eval'_obj_d, eval'_obj_d],
      simp only [universal_map.eval_Pow, free_abelian_group.lift_eq_sum, ← endomorphisms.forget_map,
        sum_comp, comp_sum, nat_trans.app_sum, functor.map_sum, whisker_right_app,
        zsmul_comp, comp_zsmul, nat_trans.app_zsmul, functor.map_zsmul],
      refine finset.sum_congr rfl _, intros g hg, refine congr_arg2 _ rfl _,
      dsimp only [endomorphisms.forget_map, functor.map_endomorphisms_map_f],
      rw [← functor.map_comp, ← functor.map_comp], congr' 1,
      dsimp only [basic_universal_map.eval_Pow_app, iso.symm_hom, Pow_X_inv],
      ext j : 2,
      rw [biproduct.ι_desc_assoc, biproduct.ι_matrix_assoc, ← endomorphisms.comp_f,
        biproduct.ι_matrix, biproduct.lift_desc],
      have := (endomorphisms.forget _).map_id ⟨X,f⟩, dsimp only [endomorphisms.forget_obj] at this,
      simp only [← endomorphisms.forget_map, ← this, ← functor.map_zsmul, ← functor.map_sum, ← functor.map_comp],
      congr' 1,
      apply biproduct.hom_ext, intro i,
      simp only [biproduct.lift_π, sum_comp, category.assoc],
      rw finset.sum_eq_single_of_mem i (finset.mem_univ _),
      { rw [biproduct.ι_π, dif_pos rfl, eq_to_hom_refl, category.comp_id], },
      { rintro k - hk, rw [biproduct.ι_π_ne _ hk, comp_zero], } }, }
end

section

variables [has_finite_limits 𝓐] [has_finite_colimits 𝓐]
variables (hH0 : ((data.eval_functor F).obj BD.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _)
variables (X : endomorphisms 𝓐)

def forget_eval :
  endomorphisms.forget _ ⋙ (data.eval_functor F).obj BD.data ≅
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ (endomorphisms.forget 𝓐).map_homological_complex _ :=
sorry

def eval'_homology :
  BD.eval' F ⋙ homology_functor 𝓐 (complex_shape.up ℤ) 0 ≅
  (data.eval_functor F).obj BD.data ⋙ homology_functor 𝓐 (complex_shape.down ℕ) 0 :=
sorry

def hH0_endo₄ :
  (BD.eval' F.map_endomorphisms ⋙
     (endomorphisms.forget 𝓐).map_homological_complex (complex_shape.up ℤ) ⋙
       homology_functor 𝓐 (complex_shape.up ℤ) 0) ≅
  (endomorphisms.forget _ ⋙ (data.eval_functor F).obj BD.data ⋙ homology_functor 𝓐 (complex_shape.down ℕ) 0) :=
sorry

def hH0_endo₃ :
  (BD.eval' F.map_endomorphisms ⋙ (endomorphisms.forget 𝓐).map_homological_complex (complex_shape.up ℤ) ⋙
    homology_functor 𝓐 (complex_shape.up ℤ) 0).obj X ≅ X.X :=
(hH0_endo₄ _ _).app _ ≪≫ hH0.app _
-- (iso_whisker_left (BD.eval' F.map_endomorphisms)
--         ((endomorphisms.forget 𝓐).homology_functor_iso (complex_shape.up ℤ) 0)).app X ≪≫
-- (hH0_endo₃ _ _ hH0 X)

def hH0_endo₁_a :
  BD.eval' F.map_endomorphisms ⋙ homology_functor _ _ 0 ⋙ endomorphisms.forget 𝓐 ≅
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ homology_functor _ _ 0 ⋙ endomorphisms.forget 𝓐 :=
((whiskering_right _ _ _).obj (endomorphisms.forget 𝓐)).map_iso (eval'_homology _ _)

def hH0_endo₁_b :
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ homology_functor _ _ 0 ⋙ endomorphisms.forget 𝓐 ≅
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ (endomorphisms.forget 𝓐).map_homological_complex _ ⋙ homology_functor _ _ 0 :=
((whiskering_left _ _ _).obj ((data.eval_functor _).obj BD.data)).map_iso
  ((endomorphisms.forget 𝓐).homology_functor_iso _ 0)

def hH0_endo₁_c :
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ (endomorphisms.forget 𝓐).map_homological_complex _ ⋙ homology_functor _ _ 0 ≅
  endomorphisms.forget _ ⋙ (data.eval_functor F).obj BD.data ⋙ homology_functor _ _ 0 :=
let e := (forget_eval BD F).symm,
    φ := ((whiskering_right _ _ _).obj (homology_functor 𝓐 (complex_shape.down ℕ) 0)).map_iso e
in sorry

def hH0_endo₁ :
  BD.eval' F.map_endomorphisms ⋙ homology_functor (endomorphisms 𝓐) _ 0 ⋙ endomorphisms.forget 𝓐 ≅
  endomorphisms.forget _ ⋙ (data.eval_functor F).obj BD.data ⋙ homology_functor 𝓐 _ 0 :=
hH0_endo₁_a _ _ ≪≫ hH0_endo₁_b _ _ ≪≫ hH0_endo₁_c _ _

def hH0_endo₂ :
  ((BD.eval' F.map_endomorphisms ⋙ homology_functor (endomorphisms 𝓐) (complex_shape.up ℤ) 0).obj X).X ≅ X.X :=
(hH0_endo₁ _ _).app _ ≪≫ hH0.app _

def hH0_endo :
  (BD.eval' F.map_endomorphisms ⋙ homology_functor (endomorphisms 𝓐) (complex_shape.up ℤ) 0).obj X ≅ X :=
endomorphisms.mk_iso (hH0_endo₂ _ _ hH0 X)
begin
  dsimp only [hH0_endo₂, iso.trans_hom, iso_whisker_left_hom, iso.app_hom, whisker_left_app],
  -- let e := ((endomorphisms.forget 𝓐).homology_functor_iso (complex_shape.up ℤ) 0).hom,
  -- have := e.naturality,
  sorry
end

/-

  { refine endomorphisms.mk_iso _ _,
    { refine _ ≪≫ hH0.app A,
      let e := iso_whisker_left (BD.eval' F.map_endomorphisms)
        ((endomorphisms.forget 𝓐).homology_functor_iso (complex_shape.up ℤ) 0),
      refine (e.app ⟨A,f⟩) ≪≫ _, clear e,
      sorry
      -- refine (endomorphisms.forget 𝓐).map_iso (homology_iso' _ (-1) 0 1 rfl rfl) ≪≫ _,
      -- refine (endomorphisms.forget 𝓐).homology_iso _ _ _ _ ≪≫ _,
      -- { rw [← functor.map_comp, homological_complex.d_comp_d, functor.map_zero], },
      -- refine (homology_iso_datum.iso _).symm,
      -- refine (homology_iso_datum.tautological' _ _ _).map_iso _ _ _ _ _,
      -- { refine arrow.iso_mk _ _ _,
      --   { refine homological_complex.X_prev_iso _ rfl ≪≫ F.map_iso _,
      --     exact (Pow_X ⟨A,f⟩ (BD.data.X 1)).symm, },
      --   { refine F.map_iso (Pow_X ⟨A,f⟩ _).symm, },
      --   { sorry } },
      -- { refine arrow.iso_mk _ _ _,
      --   { refine F.map_iso (Pow_X ⟨A,f⟩ _).symm, },
      --   { apply is_zero.iso,
      --     { apply homological_complex.X_next_is_zero, apply chain_complex.next_nat_zero, },
      --     { dsimp, apply endomorphisms.is_zero_X, apply is_zero_zero } },
      --   { sorry } },
      -- { refl },
       },
    { dsimp only [iso.trans_hom, iso.app_hom],
      have := hH0.hom.naturality f, simp only [functor.id_map] at this,
      simp only [category.assoc, ← this], simp only [← category.assoc], refine congr_arg2 _ _ rfl,
      sorry } },

-/

end

variables [has_coproducts (endomorphisms 𝓐)]
variables [AB4 (endomorphisms 𝓐)]

lemma main_lemma [has_finite_limits 𝓐] [has_finite_colimits 𝓐]
  (A : 𝓐) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B)
  (hH0 : ((data.eval_functor F).obj BD.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _)
  (T : Ab.{v} ⥤ endomorphisms 𝓐) [Π (α : Type v), preserves_colimits_of_shape (discrete α) T]
  (hT0 : T.obj (AddCommGroup.of (punit →₀ ℤ)) ≅ ⟨A, f⟩)
  (hT : ∀ {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z),
    short_exact f g → short_exact (T.map f) (T.map g))
  (hTA : ∀ t ≤ (-1:ℤ), (∃ (A' : Ab),
    nonempty (T.obj A' ≅ ((BD.eval F.map_endomorphisms).obj ⟨A, f⟩).val.as.homology t))) :
  (∀ i, is_iso $ ((Ext' i).map f.op).app B - ((Ext' i).obj (op A)).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((BD.eval F).map f).op).app ((single _ 0).obj B) -
    ((Ext i).obj (op $ (BD.eval F).obj A)).map ((single _ 0).map g)) :=
begin
  rw [← endomorphisms.Ext'_is_zero_iff' A B f g],
  erw [← endomorphisms.Ext_is_zero_iff'],
  refine (main_lemma.is_zero BD F.map_endomorphisms _ _ _ T hT0 @hT hTA).trans _,
  { exact hH0_endo _ _ hH0 _ },
  apply forall_congr, intro i,
  apply iso.is_zero_iff,
  refine functor.map_iso _ _ ≪≫ iso.app (functor.map_iso _ _) _,
  { exact (endomorphisms.mk_bo_ha_ca'_single _ _).symm, },
  { refine (mk_bo_ha_ca'_Q _ _ _ _).op, },
end

end

end package
end breen_deligne
