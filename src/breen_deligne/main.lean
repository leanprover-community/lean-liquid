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
import for_mathlib.derived.Ext_lemmas
import for_mathlib.endomorphisms.homology
import for_mathlib.yoneda_left_exact
import for_mathlib.homotopy_category_functor_compatibilities
import for_mathlib.preserves_exact
import for_mathlib.AddCommGroup.tensor

.

noncomputable theory

universes v u

open_locale big_operators
open_locale zero_object

open category_theory category_theory.limits opposite
open bounded_homotopy_category (Ext single)

namespace breen_deligne
namespace package

variables (BD : package)
variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]
variables (F : 𝓐 ⥤ 𝓐) --[preserves_filtered_colimits F]

namespace main_lemma

variables (A : 𝓐) (B : 𝓐) (j : ℤ)

def IH [enough_projectives 𝓐] : Prop :=
  (∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B) ↔
  (∀ i ≤ j, is_zero $ ((Ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B))

lemma IH_neg [enough_projectives 𝓐] (j : ℤ) (hj : j ≤ 0) : IH BD F A B (j - 1) :=
begin
  split; intros _ _ hij,
  { apply Ext_single_right_is_zero _ _ 1 _ _ (chain_complex.bounded_by_one _),
    linarith only [hj, hij] },
  { apply Ext'_is_zero_of_neg, linarith only [hj, hij] }
end

/-- the assumption hC is very suboptimal! -/
def homology_iso_deg_0_of_bounded_by_1 (C : homological_complex 𝓐 (complex_shape.up ℤ))
  (hC : ∀ (i : ℤ), 1 ≤ i → is_zero (C.X i)) : C.homology 0 ≅ cokernel (C.d_to 0) :=
begin
  refine (short_complex.homology_functor_iso 𝓐 _ 0).app C ≪≫
    (homology_iso_datum.of_g_is_zero _ _ _).iso.symm,
  dsimp,
  rw C.d_from_eq (zero_add 1),
  suffices : C.d 0 1 = 0,
  { rw [this, zero_comp], },
  apply is_zero.eq_of_tgt,
  exact hC 1 (by refl),
end

def homology_iso_deg_0_of_bounded_by_1_down (C : homological_complex 𝓐 (complex_shape.down ℤ))
  (hC : ∀ (i : ℤ), 1 ≤ i → is_zero (C.X i)) : C.homology 0 ≅ kernel (C.d_from 0) :=
begin
  refine (short_complex.homology_functor_iso 𝓐 _ 0).app C ≪≫
    (homology_iso_datum.of_f_is_zero _ _ _).iso.symm,
  dsimp,
  rw C.d_to_eq (zero_add 1),
  suffices : C.d 1 0 = 0,
  { rw [this, comp_zero], },
  apply is_zero.eq_of_src,
  exact hC 1 (by refl),
end

variables [enough_projectives 𝓐]

def IH_0_aux (C : bounded_homotopy_category 𝓐) (hC : C.val.bounded_by 1) :
  ((Ext' 0).flip.obj B).obj (op (C.val.as.homology 0)) ≅
  ((Ext 0).obj (op C)).obj ((single 𝓐 0).obj B) :=
begin
  refine (bounded_derived_category.Ext'_zero_flip_iso _ _).app _ ≪≫ _,
  refine _ ≪≫ (bounded_homotopy_category.Ext0.obj (op C)).map_iso (shift_zero _ _).symm,
  refine _ ≪≫ (bounded_homotopy_category.hom_single_iso _ _ _).symm,
  dsimp only [unop_op],
  have h := homotopy_category.exists_bounded_K_projective_replacement_of_bounded 1 C.val hC,
  let P₁ := h.some,
  have hP₁ : P₁.bounded_by 1 := h.some_spec.some_spec.some,
  haveI : P₁.is_bounded_above := ⟨⟨1, hP₁⟩⟩,
  let P : bounded_homotopy_category 𝓐 := ⟨P₁⟩,
  haveI : P.val.is_K_projective := h.some_spec.some,
  let ψ : P ⟶ C := h.some_spec.some_spec.some_spec.some,
  haveI hψ : homotopy_category.is_quasi_iso ψ := h.some_spec.some_spec.some_spec.some_spec.1,
  let e : C.replace.val ≅ P.val := (bounded_homotopy_category.forget _).map_iso
  { hom := bounded_homotopy_category.lift C.π ψ,
    inv := bounded_homotopy_category.lift ψ C.π,
    hom_inv_id' := by simp only [bounded_homotopy_category.lift_comp_lift_self,
      bounded_homotopy_category.lift_self],
    inv_hom_id' := by simp only [bounded_homotopy_category.lift_comp_lift_self,
      bounded_homotopy_category.lift_self], },
  let e' : (((preadditive_yoneda.obj B).map_homological_complex
    (complex_shape.up ℤ).symm).obj C.replace.val.as.op).homology 0 ≅
    (((preadditive_yoneda.obj B).map_homological_complex
    (complex_shape.up ℤ).symm).obj P.val.as.op).homology 0 :=
  begin
    refine _ ≪≫ (functor.map_homotopy_category (complex_shape.down ℤ)
      (preadditive_yoneda.obj B) ⋙ homotopy_category.homology_functor _ _ 0).map_iso
        (homotopy_category.op_functor.map_iso e.op.symm) ≪≫ _,
    { symmetry,
      exact (preadditive_yoneda.obj B).quotient_op_map_homology_iso C.replace.val 0, },
    { exact (preadditive_yoneda.obj B).quotient_op_map_homology_iso P.val 0, },
  end,
  refine  _ ≪≫
    (homology_iso_deg_0_of_bounded_by_1_down
      (((preadditive_yoneda.obj B).map_homological_complex
      (complex_shape.up ℤ).symm).obj P.val.as.op)
      (λ i hi, begin dsimp only [functor.map_homological_complex],
        rw is_zero.iff_id_eq_zero, rw ← (preadditive_yoneda.obj B).map_id,
        suffices : 𝟙 (P₁.as.op.X i) = 0,
        { rw [this, functor.map_zero], },
        apply quiver.hom.unop_inj, dsimp,
        simpa [← is_zero.iff_id_eq_zero] using hP₁ i hi,
      end)).symm ≪≫
    e'.symm,
  refine (preadditive_yoneda.obj B).map_iso _ ≪≫
    as_iso (kernel_comparison (P₁.as.op.d 0 (-1)) (preadditive_yoneda.obj B)) ≪≫
    (kernel.map_iso _ ((((preadditive_yoneda.obj B).map_homological_complex
      (complex_shape.up ℤ).symm).obj P.val.as.op).d 0 (-(1 : ℤ))) (iso.refl _)
    (homological_complex.X_next_iso _ (by { dsimp, refl })) (by simpa)).symm,
  refine iso.op _ ≪≫ (kernel_op_op (P₁.as.d (-1) 0)).symm,
  refine (cokernel.map_iso _ _ (P₁.as.X_prev_iso rfl) (iso.refl _)
    (begin simpa only [iso.refl_hom, category.comp_id] using P₁.as.d_to_eq _, end )).symm ≪≫
    (homology_iso_deg_0_of_bounded_by_1 P₁.as hP₁).symm ≪≫
    as_iso ((homotopy_category.homology_functor 𝓐 (complex_shape.up ℤ) 0).map ψ),
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

omit hH0

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
def bdd_step₅_aux'' {𝓐 : Type*} [category 𝓐] [abelian 𝓐] (X Y : bounded_homotopy_category 𝓐)
  (e : bounded_homotopy_category 𝓐 ≌ bounded_homotopy_category 𝓐)
  [e.functor.additive] :
  (preadditive_yoneda.obj X).obj (op Y) ≅
    (preadditive_yoneda.obj (e.functor.obj X)).obj (op (e.functor.obj Y)) :=
add_equiv.to_AddCommGroup_iso $
{ map_add' := λ f g, e.functor.map_add,
  .. equiv_of_fully_faithful e.functor }

-- move me
instance shift_equiv_functor_additive {𝓐 : Type*} [category 𝓐] [abelian 𝓐] (k : ℤ) :
  (shift_equiv (bounded_homotopy_category 𝓐) k).functor.additive :=
bounded_homotopy_category.shift_functor_additive k

def bdd_step₅_aux' {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (X Y : bounded_homotopy_category 𝓐) (k : ℤ) :
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

variables [has_coproducts.{v} 𝓐] [AB4 𝓐]

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
    refine (s.ι.app ⟨a⟩) (finsupp.single punit.star 1) },
  { rintro s ⟨a⟩, apply finsupp.add_hom_ext', rintro ⟨⟩, apply add_monoid_hom.ext_int,
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

lemma bdd_step (j : ℤ) (ih : IH BD F A B j) : IH BD F A B (j + 1) :=
begin
  by_cases ih' : (∀ i ≤ j, is_zero $ ((Ext' i).obj (op A)).obj B), swap,
  { split,
    { intro h, refine (ih' $ λ i hi, _).elim, apply h _ (int.le_add_one hi), },
    { intro h, refine (ih' $ ih.mpr $ λ i hi, _).elim, apply h _ (int.le_add_one hi), } },
  refine (bdd_step₁ BD F _ _ hH0 _).trans ((bdd_step₂ BD F _ _ _).trans _).symm,
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
  { intros k hk, exact bdd_step BD F A B hH0 T hT1 @hT hAT k },
  { intros k hk _, exact IH_neg BD F A B k hk, },
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

instance eval'_bounded_above {𝓐 : Type u} [category 𝓐] [abelian 𝓐]
  (F : 𝓐 ⥤ 𝓐) (X : 𝓐) :
  ((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj ((BD.eval' F).obj X)).is_bounded_above :=
((BD.eval F).obj X).bdd

/-
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
-/

section

def eval_mk_end (A : 𝓐) (f : A ⟶ A) :
  homological_complex.mk_end
    (((data.eval_functor F).obj BD.data).obj A)
    (((data.eval_functor F).obj BD.data).map f) ≅
  ((data.eval_functor F.map_endomorphisms).obj BD.data).obj ⟨A, f⟩ :=
begin
  refine homological_complex.hom.iso_of_components _ _,
  { intro i, refine endomorphisms.mk_iso _ _,
    { refine F.map_iso _, exact (Pow_X ⟨A,f⟩ _).symm, },
    { dsimp [homological_complex.mk_end],
      rw [← F.map_comp, ← F.map_comp], congr' 1,
      ext j,
      simp only [category.assoc, biproduct.ι_map_assoc, biproduct.map_desc_assoc,
        biproduct.ι_desc, biproduct.ι_desc_assoc],
      rw ← endomorphisms.hom.comm, } },
  { rintro _ i (rfl : _ = _), ext k,
    dsimp [homological_complex.mk_end, endomorphisms.mk_iso],
    simp only [universal_map.eval_Pow, free_abelian_group.lift_eq_sum, ← endomorphisms.forget_map,
      nat_trans.app_sum, functor.map_sum, comp_sum, sum_comp,
      nat_trans.app_zsmul, functor.map_zsmul, comp_zsmul, zsmul_comp],
    refine finset.sum_congr rfl _,
    intros x hx,
    refine congr_arg2 _ rfl _,
    dsimp only [endomorphisms.forget_map, functor.map_endomorphisms_map_f,
      whisker_right_app, basic_universal_map.eval_Pow_app],
    rw [← functor.map_comp, ← functor.map_comp], congr' 1,
    ext j : 2,
    rw [biproduct.ι_desc_assoc, biproduct.ι_matrix_assoc, ← endomorphisms.comp_f,
      biproduct.ι_matrix, biproduct.lift_desc],
    have := (endomorphisms.forget _).map_id ⟨A,f⟩, dsimp only [endomorphisms.forget_obj] at this,
    simp only [← endomorphisms.forget_map, ← this, ← functor.map_zsmul, ← functor.map_sum, ← functor.map_comp],
    congr' 1,
    apply biproduct.hom_ext, intro i,
    simp only [biproduct.lift_π, sum_comp, category.assoc],
    rw finset.sum_eq_single_of_mem i (finset.mem_univ _),
    { rw [biproduct.ι_π, dif_pos rfl, eq_to_hom_refl, category.comp_id], },
    { rintro k - hk, rw [biproduct.ι_π_ne _ hk, comp_zero], } }
end

variables (hH0 : ((data.eval_functor F).obj BD.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _)
variables (X : endomorphisms 𝓐)

def forget_eval :
  endomorphisms.forget _ ⋙ (data.eval_functor F).obj BD.data ≅
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ (endomorphisms.forget 𝓐).map_homological_complex _ :=
nat_iso.of_components (λ X, homological_complex.hom.iso_of_components
  (λ n, F.map_iso (Pow_X _ _).symm)
  begin
    rintro _ i (rfl : _=_),
    dsimp only [functor.comp_obj, data.eval_functor_obj_obj_d,
      functor.map_homological_complex_obj_d, universal_map.eval_Pow],
    simp only [free_abelian_group.lift_eq_sum,
      sum_comp, comp_sum, nat_trans.app_sum, functor.map_sum, whisker_right_app,
      zsmul_comp, comp_zsmul, nat_trans.app_zsmul, functor.map_zsmul],
    refine finset.sum_congr rfl _,
    intros x hx,
    refine congr_arg2 _ rfl _,
    dsimp only [endomorphisms.forget_map, functor.map_endomorphisms_map_f, functor.map_iso_hom,
      whisker_right_app, basic_universal_map.eval_Pow_app,
      Pow_X_inv, iso.symm_hom],
    rw [← functor.map_comp, ← functor.map_comp], congr' 1,
    ext j : 2,
    rw [biproduct.ι_desc_assoc, biproduct.ι_matrix_assoc, ← endomorphisms.comp_f,
      biproduct.ι_matrix, biproduct.lift_desc],
    have := (endomorphisms.forget _).map_id X,
    simp only [← endomorphisms.forget_map, ← this, ← functor.map_zsmul, ← functor.map_sum, ← functor.map_comp],
    congr' 1,
    apply biproduct.hom_ext, intro i,
    simp only [biproduct.lift_π, sum_comp, category.assoc],
    rw finset.sum_eq_single_of_mem i (finset.mem_univ _),
    { rw [biproduct.ι_π, dif_pos rfl, eq_to_hom_refl, category.comp_id], },
    { rintro k - hk, rw [biproduct.ι_π_ne _ hk, comp_zero], }
  end)
begin
  intros X Y f,
  ext n,
  dsimp only [homological_complex.hom.iso_of_components_hom_f,
    homological_complex.comp_f, iso.symm_hom, Pow_X_inv, functor.comp_map, functor.map_iso_hom,
    functor.map_homological_complex_map_f, data.eval_functor_obj_map_f,
    endomorphisms.forget_map, functor.map_endomorphisms_map_f],
  rw [← functor.map_comp, ← functor.map_comp], congr' 1,
  ext j : 2,
  rw [biproduct.ι_desc_assoc, biproduct.ι_map_assoc, ← endomorphisms.comp_f,
    biproduct.ι_map, biproduct.ι_desc, endomorphisms.comp_f],
end

def eval'_homology {𝓐 : Type*} [category 𝓐] [abelian 𝓐] (F : 𝓐 ⥤ 𝓐) (i : ℕ) :
  BD.eval' F ⋙ homology_functor 𝓐 (complex_shape.up ℤ) (-i) ≅
  (data.eval_functor F).obj BD.data ⋙ homology_functor 𝓐 (complex_shape.down ℕ) i :=
begin
  calc ((data.eval_functor F).obj BD.data ⋙
    homological_complex.embed complex_shape.embedding.nat_down_int_up) ⋙
    homology_functor 𝓐 (complex_shape.up ℤ) (-i) ≅
    (data.eval_functor F).obj BD.data ⋙
    homological_complex.embed complex_shape.embedding.nat_down_int_up ⋙
    homology_functor 𝓐 (complex_shape.up ℤ) (-i) : functor.associator _ _ _
  ... ≅ (data.eval_functor F).obj BD.data ⋙ homology_functor 𝓐 (complex_shape.down ℕ) i :
    iso_whisker_left _ _,
  refine homological_complex.homology_embed_nat_iso 𝓐 complex_shape.embedding.nat_down_int_up
    complex_shape.embedding.nat_down_int_up_c_iff _ _ _,
  { cases i; refl }
end

def hH_endo₁_a (i : ℕ) :
  BD.eval' F.map_endomorphisms ⋙ homology_functor _ _ (-i) ⋙ endomorphisms.forget 𝓐 ≅
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ homology_functor _ _ i ⋙ endomorphisms.forget 𝓐 :=
((whiskering_right _ _ _).obj (endomorphisms.forget 𝓐)).map_iso (eval'_homology _ _ _)

def hH_endo₁_b (i : ℕ) :
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ homology_functor _ _ i ⋙ endomorphisms.forget 𝓐 ≅
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ (endomorphisms.forget 𝓐).map_homological_complex _ ⋙ homology_functor _ _ i :=
((whiskering_left _ _ _).obj ((data.eval_functor _).obj BD.data)).map_iso
  ((endomorphisms.forget 𝓐).homology_functor_iso _ i)

def hH_endo₁_c (i : ℕ) :
  (data.eval_functor F.map_endomorphisms).obj BD.data ⋙ (endomorphisms.forget 𝓐).map_homological_complex _ ⋙ homology_functor _ _ i ≅
  endomorphisms.forget _ ⋙ (data.eval_functor F).obj BD.data ⋙ homology_functor _ _ i :=
(((whiskering_right _ _ _).obj (homology_functor 𝓐 (complex_shape.down ℕ) i)).map_iso (forget_eval BD F).symm : _)

def hH_endo₁ (i : ℕ) :
  BD.eval' F.map_endomorphisms ⋙ homology_functor (endomorphisms 𝓐) _ (-i) ⋙ endomorphisms.forget 𝓐 ≅
  endomorphisms.forget _ ⋙ (data.eval_functor F).obj BD.data ⋙ homology_functor 𝓐 _ i :=
hH_endo₁_a _ _ i ≪≫ hH_endo₁_b _ _ i ≪≫ hH_endo₁_c _ _ i

lemma hH_endo₁_natural (X : endomorphisms 𝓐) (i : ℕ) :
  ((BD.eval' F.map_endomorphisms ⋙ homology_functor _ _ (-i)).obj X).e ≫ (BD.hH_endo₁ F i).hom.app X =
    (BD.hH_endo₁ F i).hom.app X ≫ ((data.eval_functor F).obj BD.data ⋙ homology_functor 𝓐 _ i).map X.e :=
begin
  let φ : X ⟶ X := ⟨X.e, rfl⟩,
  have := (hH_endo₁ BD F i).hom.naturality φ, erw [← this], clear this,
  refine congr_arg2 _ _ rfl,
  dsimp only [functor.comp_map, endomorphisms.forget_map],
  erw endomorphisms.homology_functor_obj_e ((BD.eval' F.map_endomorphisms).obj X) (-i),
  congr' 2,
  dsimp only [package.eval'],
  ext i,
  rcases hi : complex_shape.embedding.nat_down_int_up.r i with _ | j,
  { apply is_zero.eq_of_src,
    dsimp [homological_complex.embed, homological_complex.embed.obj],
    simp only [hi],
    let zero : endomorphisms 𝓐 := ⟨0, 0⟩,
    have h : is_zero zero := by { rw is_zero.iff_id_eq_zero, ext, },
    have e' := (endomorphisms.forget 𝓐).map_iso (is_zero.iso h (is_zero_zero _)),
    refine is_zero.of_iso _ e'.symm,
    rw is_zero.iff_id_eq_zero,
    rw ← (endomorphisms.forget 𝓐).map_id,
    convert (endomorphisms.forget 𝓐).map_zero _ _,
    ext, },
  { apply endomorphisms.congr_f,
    dsimp [homological_complex.embed, homological_complex.embed.map,
      homological_complex.embed.obj],
    rw homological_complex.embed.f_of_some _ hi,
    rw ← cancel_mono (homological_complex.embed.X_iso_of_some
      (((data.eval_functor F.map_endomorphisms).obj BD.data).obj X) hi).hom,
    rw ← cancel_epi (homological_complex.embed.X_iso_of_some
      (((data.eval_functor F.map_endomorphisms).obj BD.data).obj X) hi).inv,
    simp only [category.assoc, iso.inv_hom_id, category.comp_id, iso.inv_hom_id_assoc],
    dsimp only [homological_complex.tautological_endomorphism],
    ext,
    simp only [endomorphisms.comp_f, endomorphisms.hom.comm],
    slice_lhs 1 2 { rw [← endomorphisms.comp_f, iso.inv_hom_id, endomorphisms.id_f], },
    rw category.id_comp,
    dsimp,
    congr,
    rw ← endomorphisms.end_of_e_f,
    apply endomorphisms.congr_f,
    apply biproduct.hom_ext,
    intro a,
    simpa only [biproduct.map_π, endomorphisms.end_of_e_comm], },
end

def hH0_endo₂ :
  ((BD.eval' F.map_endomorphisms ⋙ homology_functor (endomorphisms 𝓐) (complex_shape.up ℤ) 0).obj X).X ≅ X.X :=
(hH_endo₁ _ _ 0).app _ ≪≫ hH0.app _

def hH0_endo :
  (BD.eval' F.map_endomorphisms ⋙ homology_functor (endomorphisms 𝓐) (complex_shape.up ℤ) 0).obj X ≅ X :=
endomorphisms.mk_iso (hH0_endo₂ _ _ hH0 X)
begin
  dsimp only [hH0_endo₂, iso.trans_hom, iso_whisker_left_hom, iso.app_hom, whisker_left_app],
  have := hH0.hom.naturality X.e, simp only [functor.id_map] at this,
  simp only [category.assoc], erw [← this], clear this, simp only [← category.assoc],
  rw ← hH_endo₁_natural BD F X 0, refl,
end

end

variables [enough_projectives 𝓐]
variables [has_coproducts.{v} (endomorphisms 𝓐)]
variables [AB4 (endomorphisms 𝓐)]

lemma main_lemma_general
  (A : 𝓐) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B)
  (hH0 : ((BD.eval F.map_endomorphisms).obj ⟨A,f⟩).val.as.homology 0 ≅ ⟨A,f⟩)
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
  rw [← endomorphisms.Ext'_is_zero_iff A B f g],
  erw [← endomorphisms.Ext_is_zero_iff],
  refine (main_lemma.is_zero BD F.map_endomorphisms _ _ hH0 T hT0 @hT hTA).trans _,
  apply forall_congr, intro i,
  apply iso.is_zero_iff,
  refine functor.map_iso _ _ ≪≫ iso.app (functor.map_iso _ _) _,
  { exact iso.refl _, },
  { refine iso.op _, apply functor.map_iso,
    apply eval_mk_end },
end

lemma main_lemma
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
  rw [← endomorphisms.Ext'_is_zero_iff A B f g],
  erw [← endomorphisms.Ext_is_zero_iff],
  refine (main_lemma.is_zero BD F.map_endomorphisms _ _ _ T hT0 @hT hTA).trans _,
  { exact hH0_endo _ _ hH0 _ },
  apply forall_congr, intro i,
  apply iso.is_zero_iff,
  refine functor.map_iso _ _ ≪≫ iso.app (functor.map_iso _ _) _,
  { exact iso.refl _, },
  { refine iso.op _, apply functor.map_iso,
    apply eval_mk_end },
end

@[simps]
def endo_T {𝓐 : Type*} [category 𝓐] (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) :
  endomorphisms 𝓐 ⥤ Ab.{v} ⥤ endomorphisms 𝓐 :=
functor.flip
{ obj := λ A, (T.flip.obj A).map_endomorphisms,
  map := λ A B f, nat_trans.map_endomorphisms $ T.flip.map f,
  map_id' := by { intros X, simp only [category_theory.functor.map_id], refl},
  map_comp' := by { intros X Y Z f g, simp only [functor.map_comp], refl } }

def endo_T_comp_forget {𝓐 : Type*} [category 𝓐] (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) (M : endomorphisms 𝓐) :
  (endo_T T).obj M ⋙ endomorphisms.forget _ ≅ T.obj M.X :=
nat_iso.of_components (λ _, iso.refl _) $
by { intros, dsimp, simp only [category.comp_id, category.id_comp], }

instance endo_T_additive {𝓐 : Type*} [category 𝓐] [preadditive 𝓐]
  (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) (A : endomorphisms 𝓐) [(T.obj A.X).additive] :
  ((endo_T T).obj A).additive :=
{ map_add' := λ X Y f g, by { ext, dsimp, rw functor.map_add } }

instance endo_T_preserves_finite_limits {𝓐 : Type*} [category 𝓐]
  (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) (A : endomorphisms 𝓐)
  [preserves_finite_limits (T.obj A.X)] :
  preserves_finite_limits ((endo_T T).obj A) :=
begin
  constructor, introsI J hJ1 hJ2,
  haveI : reflects_limits_of_shape J (endomorphisms.forget 𝓐) := {},
  haveI : preserves_limits_of_shape J ((endo_T T).obj A ⋙ endomorphisms.forget 𝓐),
  { apply preserves_limits_of_shape_of_nat_iso (endo_T_comp_forget T A).symm,
    apply_instance, },
  exact preserves_limits_of_shape_of_reflects_of_preserves
    ((endo_T T).obj A) (endomorphisms.forget _),
end

set_option pp.universes true

instance endo_T_preserves_finite_colimits {𝓐 : Type u} [category.{v} 𝓐]
  (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) (A : endomorphisms 𝓐)
  [preserves_finite_colimits (T.obj A.X)] :
  preserves_finite_colimits ((endo_T T).obj A) :=
begin
  constructor, introsI J hJ1 hJ2,
  -- Move this
  haveI : reflects_colimits_of_shape J (endomorphisms.forget 𝓐),
  { let E : J ≌ as_small.{v} J := as_small.equiv,
    suffices : reflects_colimits_of_shape (as_small.{v} J) (endomorphisms.forget 𝓐),
    { resetI, apply reflects_colimits_of_shape_of_equiv E.symm, },
    constructor },
  haveI : preserves_colimits_of_shape J ((endo_T T).obj A ⋙ endomorphisms.forget 𝓐),
  { apply preserves_colimits_of_shape_of_nat_iso (endo_T_comp_forget T A).symm,
    apply_instance, },
  exact preserves_colimits_of_shape_of_reflects_of_preserves
    ((endo_T T).obj A) (endomorphisms.forget _),
end

instance endo_T_preserves_colimits_of_shape_discrete
  {𝓐 : Type u} [category.{v} 𝓐]
  (α : Type v) (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) (M : endomorphisms 𝓐)
  [preserves_colimits_of_shape (discrete α) (T.obj M.X)] :
  preserves_colimits_of_shape (discrete α) ((endo_T T).obj M) :=
begin
  letI : reflects_colimits_of_shape (discrete α) (endomorphisms.forget 𝓐) := {},
  letI : preserves_colimits_of_shape (discrete α) ((endo_T T).obj M ⋙ endomorphisms.forget 𝓐),
  { apply preserves_colimits_of_shape_of_nat_iso (endo_T_comp_forget T M).symm,
    apply_instance, },
  exact preserves_colimits_of_shape_of_reflects_of_preserves
    ((endo_T T).obj M) (endomorphisms.forget _),
end

lemma endo_T_short_exact
  {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]
  [has_products_of_shape (ulift.{v} ℕ) 𝓐] [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐]
  (A : endomorphisms 𝓐) (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) [(T.obj A.X).additive]
  [preserves_finite_limits (T.obj A.X)] [preserves_finite_colimits (T.obj A.X)]
  {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g) :
  short_exact (((endo_T T).obj A).map f) (((endo_T T).obj A).map g) :=
begin
  apply functor.map_short_exact, exact hfg
end

lemma main_lemma'
  (A : 𝓐) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B)
  (hH0 : ((data.eval_functor F).obj BD.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _)
  (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) [(T.obj A).additive]
  [preserves_finite_limits (T.obj A)] [preserves_finite_colimits (T.obj A)]
  [Π (α : Type v), preserves_colimits_of_shape (discrete α) (T.obj A)]
  (hT0 : T.flip.obj (AddCommGroup.of (punit →₀ ℤ)) ≅ 𝟭 _)
  (hTA : ∀ (t : ℤ), t ≤ -1 → (∃ (A' : Ab),
     nonempty (((endo_T T).obj ⟨A,f⟩).obj A' ≅ ((BD.eval F.map_endomorphisms).obj ⟨A,f⟩).val.as.homology t))) :
  (∀ i, is_iso $ ((Ext' i).map f.op).app B - ((Ext' i).obj (op A)).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((BD.eval F).map f).op).app ((single _ 0).obj B) -
    ((Ext i).obj (op $ (BD.eval F).obj A)).map ((single _ 0).map g)) :=
begin
  let M : endomorphisms 𝓐 := ⟨A,f⟩,
  apply BD.main_lemma F A B f g hH0 ((endo_T T).obj M),
  { exact endomorphisms.mk_iso (hT0.app _) (nat_trans.naturality _ _) },
  { intros X Y Z _ _ hfg, refine endo_T_short_exact _ T _ _ hfg, },
  { exact hTA }
end

lemma main_lemma_general'
  (A : 𝓐) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B)
  (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) [(T.obj A).additive]
  [preserves_finite_limits (T.obj A)] [preserves_finite_colimits (T.obj A)]
  [Π (α : Type v), preserves_colimits_of_shape (discrete α) (T.obj A)]
  (hT0 : T.flip.obj (AddCommGroup.of (punit →₀ ℤ)) ≅ 𝟭 _)
  (A' : ℕ → Ab)
  (hA'0 : T.flip.obj (A' 0) ≅ 𝟭 _)
  (hTA : ∀ n, (((endo_T T).obj ⟨A,f⟩).obj (A' n) ≅ ((BD.eval F.map_endomorphisms).obj ⟨A,f⟩).val.as.homology (-n))) :
  (∀ i, is_iso $ ((Ext' i).map f.op).app B - ((Ext' i).obj (op A)).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((BD.eval F).map f).op).app ((single _ 0).obj B) -
    ((Ext i).obj (op $ (BD.eval F).obj A)).map ((single _ 0).map g)) :=
begin
  let M : endomorphisms 𝓐 := ⟨A,f⟩,
  -- let h
  apply BD.main_lemma_general F A B f g _ ((endo_T T).obj M),
  { exact endomorphisms.mk_iso (hT0.app _) (nat_trans.naturality _ _) },
  { intros X Y Z _ _ hfg, refine endo_T_short_exact _ T _ _ hfg, },
  { intros t ht,
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = -n,
    { lift -t to ℕ with n hn, swap, { rw [neg_nonneg], refine ht.trans _, dec_trivial },
      refine ⟨n, _⟩, rw [hn, neg_neg], },
    refine ⟨A' n, ⟨hTA n⟩⟩, },
  { refine (hTA 0).symm ≪≫ _,
    refine endomorphisms.mk_iso (hA'0.app _) (hA'0.hom.naturality f), }
end

end

end package
end breen_deligne
