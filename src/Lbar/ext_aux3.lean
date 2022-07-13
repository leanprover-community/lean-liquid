import Lbar.ext_aux2
import Lbar.iota

noncomputable theory

universes v u u'

open opposite category_theory category_theory.limits category_theory.preadditive
open_locale nnreal zero_object

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

open bounded_homotopy_category

variables {r'}
variables (BD : breen_deligne.package)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.data.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

section preps

variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]
variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

set_option pp.universes true

lemma cofan_point_iso_colimit_conj_eq_desc
  {e : (homotopy_category.colimit_cofan
     (λ (a : ulift ℕ), ((λ (k : ulift ℕ),
     (QprimeFP r' BD.data κ₂ M).obj (ι k)) a).val)).X.is_bounded_above} :
  (cofan_point_iso_colimit
    (λ (k : ulift ℕ), (QprimeFP r' BD.data κ₂ M).obj (ι k))).inv ≫
  of_hom (sigma_shift ι hι (QprimeFP_int r' BD.data κ₂ M)) ≫
    (cofan_point_iso_colimit (λ (k : ulift ℕ),
    (QprimeFP r' BD.data κ₂ M).obj (ι k))).hom =
  begin
    apply sigma.desc,
    intros k,
    refine _ ≫ sigma.ι _ (ulift.up $ ulift.down k + 1),
    refine (QprimeFP r' BD.data κ₂ M).map _,
    refine hom_of_le (hι _),
    exact_mod_cast k.down.le_succ,
  end :=
begin
  ext j,
  dsimp only [cofan_point_iso_colimit],
  rw [colimit.ι_desc, cofan.mk_ι_app,
      colimit.comp_cocone_point_unique_up_to_iso_inv_assoc],
  simp only [← category.assoc], rw [← iso.eq_comp_inv], simp only [category.assoc],
  rw [colimit.comp_cocone_point_unique_up_to_iso_inv],
  dsimp only [sigma_shift, bounded_homotopy_category.cofan, cofan.mk_ι_app,
    of_hom, homotopy_category.colimit_cofan],
  erw [← functor.map_comp, colimit.ι_desc],
  dsimp only [sigma_shift_cone, discrete.nat_trans_app],
  refine functor.map_comp _ _ _,
end

def pi_Ext_iso_Ext_sigma (i : ℤ) :
  (∏ λ (k : ulift ℕ), ((QprimeFP r' BD.data κ₂ M).op ⋙
    (Ext i).flip.obj ((single (Condensed Ab) 0).obj V.to_Cond)).obj (op (ι k))) ≅
  ((Ext i).obj (op (of' (∐ λ (k : ulift ℕ), (QprimeFP_int r' BD.data κ₂ M).obj (ι k))))).obj
    ((single (Condensed Ab) 0).obj (Condensed.of_top_ab ↥V)) :=
(Ext_coproduct_iso
  (λ k : ulift ℕ, (QprimeFP r' BD.data κ₂ M).obj (ι k)) i
  ((single (Condensed Ab) 0).obj V.to_Cond)).symm ≪≫
  ((Ext i).flip.obj ((single (Condensed Ab) 0).obj V.to_Cond)).map_iso
begin
  refine iso.op (cofan_point_iso_colimit
    (λ (k : ulift ℕ), (QprimeFP r' BD.data κ₂ M).obj (ι k)))
end

-- move me
@[simp] lemma _root_.category_theory.op_nsmul
  {C : Type*} [category C] [preadditive C] {X Y : C} (n : ℕ) (f : X ⟶ Y) :
  (n • f).op = n • f.op := rfl

-- move me
@[simp] lemma _root_.category_theory.op_sub
  {C : Type*} [category C] [preadditive C] {X Y : C} (f g : X ⟶ Y) :
  (f - g).op = f.op - g.op := rfl

@[simp] lemma _root_.homological_complex.of_hom_sub
  {C : Type*} [category C] [abelian C]
  (X Y : homological_complex C (complex_shape.up ℤ)) (f g : X ⟶ Y)
  [((homotopy_category.quotient C (complex_shape.up ℤ)).obj X).is_bounded_above]
  [((homotopy_category.quotient C (complex_shape.up ℤ)).obj Y).is_bounded_above] :
  of_hom (f - g) = of_hom f - of_hom g := rfl

@[reassoc]
lemma Ext_coproduct_iso_naturality_inv
  (A : Type u)
  [category.{v} A]
  [abelian A]
  [enough_projectives A]
  [has_coproducts A]
  [AB4 A]
  {α : Type v}
  (X₁ X₂ : α → bounded_homotopy_category A)
  [uniformly_bounded X₁]
  [uniformly_bounded X₂]
  (g : X₁ ⟶ X₂)
  (i : ℤ) (Y) :
  (Ext_coproduct_iso _ _ _).inv ≫
  ((Ext i).map (sigma.desc (λ b, g b ≫ sigma.ι X₂ b) : ∐ X₁ ⟶ ∐ X₂).op).app Y =
  pi.lift (λ b, pi.π _ b ≫ ((Ext i).map (g b).op).app Y) ≫ (Ext_coproduct_iso _ _ _).inv :=
begin
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv],
  apply Ext_coproduct_iso_naturality,
end

end preps

