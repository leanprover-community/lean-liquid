import for_mathlib.derived.les2

noncomputable theory

universes v u

open category_theory category_theory.limits

variables {A : Type u} [category.{v} A] [abelian A]

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)

namespace bounded_homotopy_category
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)


section
open homotopy_category

-- move me
@[reassoc]
lemma Ext_map_Ext_iso [enough_projectives A]
  (i : ℤ) (P₁ P₂ X₁ X₂ Y : bounded_homotopy_category A)
  [is_K_projective P₁.val] [is_K_projective P₂.val]
  (f₁ : P₁ ⟶ X₁) [is_quasi_iso f₁] (f₂ : P₂ ⟶ X₂) [is_quasi_iso f₂]
  (φ : X₁ ⟶ X₂) (φ' : P₁ ⟶ P₂) (h : φ' ≫ f₂ = f₁ ≫ φ) :
  ((Ext i).flip.obj Y).map φ.op ≫ (Ext_iso i P₁ X₁ Y f₁).hom =
    (Ext_iso i P₂ X₂ Y f₂).hom ≫ (preadditive_yoneda.obj (Y⟦i⟧)).map φ'.op :=
begin
  dsimp only [Ext_iso, functor.map_iso_hom, iso.op_hom, Ext, Ext0,
    functor.flip_obj_map, functor.comp_map, whiskering_left_obj_map, whisker_left_app,
    functor.flip_map_app],
  rw [← category_theory.functor.map_comp, ← op_comp,
      ← category_theory.functor.map_comp, ← op_comp],
  congr' 2,
  dsimp only [replacement_iso_hom, opposite.unop_op],
  refine lift_ext X₂.π _ _ _,
  simp only [category.assoc, lift_lifts, lift_lifts_assoc, quiver.hom.unop_op, h],
end

-- move me
@[reassoc]
lemma Ext_map_Ext_iso' [enough_projectives A]
  (i : ℤ) (X₁ X₂ Y : bounded_homotopy_category A) (φ : X₁ ⟶ X₂) :
  ((Ext i).flip.obj Y).map φ.op ≫ (Ext_iso i _ X₁ Y X₁.π).hom =
    (Ext_iso i _ X₂ Y X₂.π).hom ≫ (preadditive_yoneda.obj (Y⟦i⟧)).map (lift (X₁.π ≫ φ) X₂.π).op :=
Ext_map_Ext_iso _ _ _ _ _ _ _ _ _ _ $ by rw [lift_lifts]

lemma Ext_iso_naturality_snd_component
  [enough_projectives A]
  (i : ℤ) (P X Y₁ Y₂ : bounded_homotopy_category A)
  [is_K_projective P.val]
  (f : P ⟶ X) [is_quasi_iso f] (g : Y₁ ⟶ Y₂) :
  ((Ext i).obj _).map g ≫ (Ext_iso i P X _ f).hom =
  (Ext_iso i P X _ f).hom ≫ (preadditive_yoneda.flip.obj (opposite.op P)).map (g⟦i⟧') :=
begin
  dsimp only [Ext_iso, Ext, Ext0], ext t,
  dsimp, simp only [comp_apply], dsimp, simp,
end

end

def shift_iso [enough_projectives A]
  (n : ℤ) (X : cochain_complex A ℤ) (Y : bounded_homotopy_category A)
  [((homotopy_category.quotient A (complex_shape.up ℤ)).obj X).is_bounded_above] :
  (((Ext (n+1)).flip.obj Y)).obj (opposite.op $ (of' X)⟦(1:ℤ)⟧) ≅
  (((Ext n).flip.obj Y)).obj (opposite.op $ (of' X)) :=
begin
  let e := Ext_iso n (of' X).replace (of' X) Y (of' X).π,
  let e' := Ext_iso (n+1) ((of' X).replace⟦1⟧) ((of' X)⟦1⟧) Y ((of' X).π⟦(1:ℤ)⟧'),
  refine (e' ≪≫ _ ≪≫ e.symm),
  clear e e',
  refine add_equiv.to_AddCommGroup_iso _,
  refine shift_iso_aux 1 n _ _,
end

open category_theory.preadditive

lemma shift_iso_conj
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)] :
  (shift_iso _ _ _).inv ≫ (((Ext (n+1)).flip.obj W).right_op.map ((of_hom f)⟦(1 : ℤ)⟧')).unop
    ≫ (shift_iso _ _ _).hom =
  ((Ext n).flip.obj W).map (of_hom f).op :=
begin
  dsimp only [shift_iso, iso.trans_hom, iso.trans_inv, iso.symm_inv, iso.symm_hom,
    functor.right_op_map, quiver.hom.unop_op],
  simp only [category.assoc],
  rw [Ext_map_Ext_iso_assoc (n+1)
    ((shift_functor (bounded_homotopy_category A) (1:ℤ)).obj (of' X).replace)
    ((shift_functor (bounded_homotopy_category A) (1:ℤ)).obj (of' Y).replace)
    _ _ _
    ((shift_functor (bounded_homotopy_category A) 1).map (of' X).π)
    ((shift_functor (bounded_homotopy_category A) 1).map (of' Y).π)
    _ ((lift ((of' X).π ≫ of_hom f) (of' Y).π)⟦1⟧'),
    iso.inv_hom_id_assoc],
  swap,
  { simp only [comp_neg, neg_comp, neg_inj, ← category_theory.functor.map_comp, lift_lifts], },
  simp only [← category.assoc, iso.comp_inv_eq],
  rw [Ext_map_Ext_iso', category.assoc, category.assoc], congr' 1,
  rw [← category.assoc, ← iso.eq_comp_inv],
  apply AddCommGroup.ext, intros φ,
  dsimp only [shift_iso_aux, add_equiv.to_AddCommGroup_iso],
  rw [comp_apply, comp_apply],
  dsimp only [add_equiv.coe_to_add_monoid_hom, add_equiv.symm, equiv.symm, add_equiv.to_equiv_mk,
    add_equiv.coe_mk],
  erw [preadditive_yoneda_obj_map_apply, preadditive_yoneda_obj_map_apply],
  simp only [← category.assoc, quiver.hom.unop_op, ← category_theory.functor.map_comp],
end

--attribute [simps] shift_iso_aux
lemma shift_iso_conj'
  (n : ℤ)
  [enough_projectives A]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  (W₁ W₂ : bounded_homotopy_category A) (f : W₁ ⟶ W₂) :
  (shift_iso n X W₁).inv ≫ ((Ext (n+1)).obj _).map f ≫ (shift_iso n X _).hom =
  ((Ext n).obj _).map f :=
begin
  dsimp only [shift_iso, iso.trans_hom, iso.trans_inv, iso.symm_hom, iso.symm_inv],
  simp only [category.assoc],
  slice_lhs 4 5 { rw Ext_iso_naturality_snd_component },
  simp only [category.assoc, iso.inv_hom_id_assoc, category.id_comp],
  rw ← iso.eq_inv_comp,
  simp_rw ← category.assoc,
  rw iso.comp_inv_eq,
  simp_rw category.assoc,
  rw Ext_iso_naturality_snd_component,
  rw iso.inv_hom_id_assoc,
  ext t,
  dsimp,
  simp only [comp_apply],
  dsimp,
  simp only [add_zero, unit_of_tensor_iso_unit_inv_app,
    discrete.functor_map_id, nat_trans.id_app, category.id_comp, category.assoc,
    nat_trans.naturality, functor.comp_map, μ_hom_inv_app_assoc, functor.map_comp,
    ε_inv_app_obj, discrete.right_unitor_def, eq_to_iso.hom, eq_to_hom_map,
    eq_to_hom_app, μ_naturality_assoc, μ_inv_hom_app_assoc],
  erw ← nat_trans.naturality_assoc,
  erw ← nat_trans.naturality_assoc,
  dsimp, let s := _, change _ ≫ _ ≫ s = _, rw ← category.assoc, convert category.comp_id _,
  dsimp [s],
  simp only [eq_to_hom_map, eq_to_hom_app, eq_to_iso.inv, ε_app_obj, discrete.right_unitor_def,
    category.assoc, μ_inv_hom_app_assoc, eq_to_hom_trans, eq_to_hom_refl],
end

@[reassoc] lemma shift_iso_Ext_map
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)] :
  (((Ext (n+1)).flip.obj W).right_op.map ((of_hom f)⟦(1 : ℤ)⟧')).unop ≫ (shift_iso _ _ _).hom =
  (shift_iso _ _ _).hom ≫ ((Ext n).flip.obj W).map (of_hom f).op :=
by rw [← iso.inv_comp_eq, shift_iso_conj]

@[reassoc] lemma Ext_map_shift_iso_inv
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)] :
  (shift_iso _ _ _).inv ≫ (((Ext (n+1)).flip.obj W).right_op.map ((of_hom f)⟦(1 : ℤ)⟧')).unop =
  ((Ext n).flip.obj W).map (of_hom f).op ≫ (shift_iso _ _ _).inv :=
by rw [iso.eq_comp_inv, category.assoc, shift_iso_conj]

def Ext_δ
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w : ∀ i, short_exact (f.f i) (g.f i)) :
  ((Ext n).flip.obj W).obj (opposite.op $ of' X) ⟶
  ((Ext (n+1)).flip.obj W).obj (opposite.op $ of' Z) :=
(shift_iso n X W).inv ≫ (connecting_hom' f g (n+1) W w).unop

.

def map_cone {A₁ A₂ B₁ B₂ : cochain_complex A ℤ}
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj A₁)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj B₁)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj A₂)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj B₂)]
  (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂) (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (sq : f₁ ≫ b = a ≫ f₂) :
  cone f₁ ⟶ cone f₂ :=
(homotopy_category.quotient _ _).map $
{ f := λ i, biprod.lift (biprod.fst ≫ a.f _) (biprod.snd ≫ b.f _),
  comm' := begin
    rintros i j ⟨⟨rfl⟩⟩,
    ext,
    { dsimp [homological_complex.cone.d], simp },
    { dsimp [homological_complex.cone.d], simp,
      simp only [← homological_complex.comp_f, sq] },
    { dsimp [homological_complex.cone.d], simp },
    { dsimp [homological_complex.cone.d], simp },
  end }

.

lemma Ext_δ_natural
  (i : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  {X₁ Y₁ Z₁ : cochain_complex A ℤ} (f₁ : X₁ ⟶ Y₁) (f₂ : Y₁ ⟶ Z₁)
  {X₂ Y₂ Z₂ : cochain_complex A ℤ} (g₁ : X₂ ⟶ Y₂) (g₂ : Y₂ ⟶ Z₂)
  (α₁ : X₁ ⟶ X₂) (α₂ : Y₁ ⟶ Y₂) (α₃ : Z₁ ⟶ Z₂)
  (sq₁ : f₁ ≫ α₂ = α₁ ≫ g₁) (sq₂ : f₂ ≫ α₃ = α₂ ≫ g₂)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X₁)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y₁)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z₁)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X₂)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y₂)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z₂)]
  (w₁ : ∀ i, short_exact (f₁.f i) (f₂.f i))
  (w₂ : ∀ i, short_exact (g₁.f i) (g₂.f i)) :
  ((Ext i).flip.obj W).map (of_hom α₁).op ≫ Ext_δ f₁ f₂ i W w₁ =
    Ext_δ g₁ g₂ i W w₂ ≫ ((Ext (i + 1)).flip.obj W).map (of_hom α₃).op :=
begin
  -- TODO: This proof is SLOW.
  delta Ext_δ,
  let F := homotopy_category.quotient A (complex_shape.up ℤ),
  simp only [category.assoc],
  dsimp only [connecting_hom', unop_comp],
  simp only [unop_inv, category.assoc],
  simp only [← category.assoc, is_iso.comp_inv_eq],
  simp only [category.assoc],
  dsimp only [functor.right_op, quiver.hom.unop_op, functor.flip, opposite.unop_op],
  let t := _, change _ = _ ≫ _ ≫ t,
  have ht : t = ((Ext (i+1)).map (quiver.hom.op _)).app W,
  rotate 2,
  { apply map_cone,
    exact sq₁ },
  { -- Move the inv, and this should be doable.
    dsimp [t], rw is_iso.inv_comp_eq,
    ext f,
    dsimp [Ext, shift_iso, Ext_iso, preadditive_yoneda_obj, linear_map.to_add_monoid_hom],
    simp only [comp_apply], dsimp,
    simp only [← category.assoc],
    congr' 1,
    apply lift_ext (of' Z₂).π, swap, apply_instance,
    simp only [category.assoc, lift_lifts, lift_lifts_assoc],
    congr' 1, dsimp [map_cone, cone.π, homotopy_category.cone.π],
    erw [← F.map_comp, ← F.map_comp], congr' 1,
    dsimp [homological_complex.cone.π],
    ext,
    { simp },
    { simp,
      simp only [← homological_complex.comp_f, sq₂] } },
  rw ht, clear ht, clear t,
  ext f,
  dsimp [Ext, shift_iso, Ext_iso, preadditive_yoneda_obj, linear_map.to_add_monoid_hom],
  dsimp only [shift_iso_aux, add_equiv.symm],
  simp only [comp_apply],
  dsimp,
  simp only [← category.assoc], congr' 1,
  simp only [functor.map_comp, ← category.assoc], congr' 1,
  simp only [category.assoc],
  apply lift_ext (((of' X₂).π)⟦(1 : ℤ)⟧'),
  swap, apply_instance,
  simp only [category.assoc, ← functor.map_comp, lift_lifts],
  simp only [functor.map_comp, lift_lifts_assoc, lift_lifts, category.assoc],
  congr' 1,
  dsimp [cone_triangle, map_cone],
  simp only [comp_neg, neg_comp], congr' 1,
  erw [← F.map_comp, ← F.map_comp], congr' 1,
  dsimp [homological_complex.cone.out],
  ext,
  { simp, },
  { simp, }
end

.

lemma Ext_δ_natural'
  (i : ℤ)
  [enough_projectives A]
  (W₁ W₂ : bounded_homotopy_category A)
  (e : W₁ ⟶ W₂)
  {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w : ∀ i, short_exact (f.f i) (g.f i)) :
  ((Ext i).obj _).map e ≫ Ext_δ f g i W₂ w =
  Ext_δ f g i W₁ w ≫ ((Ext (i+1)).obj _).map e :=
begin
  delta Ext_δ,
  dsimp [connecting_hom'],
  simp only [quiver.hom.unop_op, unop_inv],
  simp_rw ← category.assoc,
  rw is_iso.comp_inv_eq,
  simp_rw category.assoc,
  let t := _, change _ = _ ≫ _ ≫ t,
  have ht : t = ((Ext (i + 1)).obj _).map e,
  { dsimp only [t],
    rw [is_iso.inv_comp_eq, nat_trans.naturality] },
  rw ht, clear ht t,
  rw iso.eq_inv_comp,
  rw ← nat_trans.naturality,
  simp only [← category.assoc],
  congr' 1,
  rw [iso.comp_inv_eq, ← shift_iso_conj', iso.hom_inv_id_assoc],
end

lemma Ext_five_term_exact_seq'
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w : ∀ i, short_exact (f.f i) (g.f i)) :
  let E := λ n, ((Ext n).flip.obj W) in
  exact_seq Ab.{v} $
    [ (E n).map (of_hom g).op
    , (E n).map (of_hom f).op
    , Ext_δ f g n W w
    , (E (n+1)).map (of_hom g).op ] :=
begin
  refine (Ext_five_term_exact_seq f g n W w).pair.unop.cons _,
  refine exact.cons _ (exact.exact_seq _),
  { rw [Ext_δ, functor.right_op_map, quiver.hom.unop_op, ← shift_iso_conj f n W,
      exact_iso_comp, exact_comp_hom_inv_comp_iff],
    have := (Ext_five_term_exact_seq f g (n+1) W w).unop.pair,
    erw [functor.map_neg, category_theory.unop_neg, abelian.exact_neg_left_iff] at this,
    exact this },
  { rw [Ext_δ, exact_iso_comp],
    exact ((Ext_five_term_exact_seq f g (n+1) W w).drop 1).pair.unop, }
end

end bounded_homotopy_category

namespace bounded_derived_category

variables [enough_projectives A]
variables {X Y Z : bounded_derived_category A} (f : X ⟶ Y) (g : Y ⟶ Z)
open homological_complex

def cone (f : X ⟶ Y) : bounded_derived_category A :=
(localization_functor _).obj $
{ val := homotopy_category.cone f.val.out,
  bdd := begin
    obtain ⟨a,ha⟩ := homotopy_category.is_bounded_above.cond X.val.val,
    obtain ⟨b,hb⟩ := homotopy_category.is_bounded_above.cond Y.val.val,
    constructor, use (max a b + 1),
    intros t ht,
    apply is_zero_biprod,
    { apply ha, refine le_trans (le_trans _ ht) _,
      refine le_trans (le_max_left a b) _,
      all_goals { linarith } },
    { apply hb,
      refine le_trans _ ht, refine le_trans (le_max_right a b) _,
      linarith }
  end }

-- UGH
end bounded_derived_category

-- move me
instance single_is_bounded_above (X : A) :
  homotopy_category.is_bounded_above {as := (homological_complex.single A (complex_shape.up ℤ) 0).obj X} :=
begin
  refine ⟨⟨1, _⟩⟩,
  intros i hi,
  dsimp,
  rw if_neg,
  { exact is_zero_zero _ },
  { rintro rfl, exact zero_lt_one.not_le hi }
end

-- move me
instance quotient_single_is_bounded_above (X : A) :
  ((homotopy_category.quotient A (complex_shape.up ℤ)).obj
    ((homological_complex.single A (complex_shape.up ℤ) 0).obj X)).is_bounded_above :=
single_is_bounded_above X

def Ext'_δ [enough_projectives A]
  {X Y Z : A} (W : A) {f : X ⟶ Y} {g : Y ⟶ Z}
  (h : short_exact f g) (n : ℤ) :
  ((Ext' n).flip.obj W).obj (opposite.op $ X) ⟶
  ((Ext' (n+1)).flip.obj W).obj (opposite.op $ Z) :=
begin
  refine @bounded_homotopy_category.Ext_δ _ _ _ _ _ _
    ((homological_complex.single _ _ _).map f)
    ((homological_complex.single _ _ _).map g)
    n _ _
    (quotient_single_is_bounded_above _)
    (quotient_single_is_bounded_above _)
    (quotient_single_is_bounded_above _) _,
  intro i, dsimp, by_cases hi : i = 0,
  { subst i, dsimp, simp only [eq_self_iff_true, category.comp_id, category.id_comp, if_true, h] },
  { rw [dif_neg hi, dif_neg hi, if_neg hi, if_neg hi, if_neg hi],
    refine ⟨exact_of_zero _ _⟩, }
end

lemma Ext'_δ_natural [enough_projectives A]
  {X₁ X₂ X₃ Y₁ Y₂ Y₃ : A}
  (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
  (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)
  (α₁ : X₁ ⟶ Y₁) (α₂ : X₂ ⟶ Y₂) (α₃ : X₃ ⟶ Y₃)
  (sq₁ : f₁ ≫ α₂ = α₁ ≫ g₁) (sq₂ : f₂ ≫ α₃ = α₂ ≫ g₂)
  (Z : A) (hf : short_exact f₁ f₂) (hg : short_exact g₁ g₂) (i : ℤ) :
  ((Ext' i).flip.obj Z).map α₁.op ≫ Ext'_δ Z hf i =
    Ext'_δ Z hg i ≫ ((Ext' (i+1)).flip.obj Z).map α₃.op :=
begin
  delta Ext' Ext'_δ,
  apply bounded_homotopy_category.Ext_δ_natural _ _ _ _ _ _ _
    ((homological_complex.single A (complex_shape.up ℤ) 0).map α₂),
  all_goals { simp only [← category_theory.functor.map_comp, sq₁, sq₂, quiver.hom.unop_op] },
end

namespace category_theory
namespace short_exact

lemma Ext'_five_term_exact_seq [enough_projectives A]
  {X Y Z : A} (W : A) {f : X ⟶ Y} {g : Y ⟶ Z}
  (h : short_exact f g) (n : ℤ) :
  let E := λ n, ((Ext' n).flip.obj W) in
  exact_seq Ab.{v} $
    [ (E n).map g.op
    , (E n).map f.op
    , Ext'_δ W h n
    , (E (n+1)).map g.op ] :=
begin
  let f' := (homological_complex.single _ (complex_shape.up ℤ) (0:ℤ)).map f,
  let g' := (homological_complex.single _ (complex_shape.up ℤ) (0:ℤ)).map g,
  let W' := (bounded_homotopy_category.single _ 0).obj W,
  have Hfg : ∀ (i : ℤ), short_exact (f'.f i) (g'.f i),
  { intro i, dsimp, by_cases hi : i = 0,
    { subst i, dsimp, simp only [eq_self_iff_true, category.comp_id, category.id_comp, if_true, h] },
    { rw [dif_neg hi, dif_neg hi, if_neg hi, if_neg hi, if_neg hi],
      refine ⟨exact_of_zero _ _⟩, } },
  convert bounded_homotopy_category.Ext_five_term_exact_seq' f' g' n W' Hfg,
end

end short_exact
end category_theory
