import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import for_mathlib.derived.homological
import for_mathlib.derived.bounded_homotopy_category
import category_theory.abelian.projective
import for_mathlib.snake_lemma3
import for_mathlib.les_homology
import for_mathlib.exact_seq3
import for_mathlib.triangle_shift
import for_mathlib.homology_iso
import for_mathlib.projective_replacement
import for_mathlib.derived.lemmas
-- import for_mathlib.arrow_preadditive

import hacks_and_tricks.asyncI

noncomputable theory

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

namespace bounded_homotopy_category

local notation `𝒦` := bounded_homotopy_category A

section enough_projectives

abbreviation uniformly_bounded {α : Type*} (X : α → 𝒦) : Prop :=
homotopy_category.is_uniformly_bounded_above (val ∘ X)

variable [enough_projectives A]

-- Main theorem about existence of K-projective replacements.
-- Perhaps all we need is this for bounded complexes, in which case we should
-- add an additional typeclass parameter here.
theorem exists_K_projective_replacement (X : 𝒦) :
  ∃ (P : 𝒦) [homotopy_category.is_K_projective P.val] (f : P ⟶ X),
  homotopy_category.is_quasi_iso f ∧ ∀ k, projective (P.val.as.X k) :=
begin
  obtain ⟨P,h1,h2,f,h3⟩ :=
    homotopy_category.exists_K_projective_replacement_of_bounded X.val,
  resetI,

  exact ⟨⟨P⟩, h1, f, h3⟩,
end

theorem exists_uniform_K_projective_replacement {α : Type*} (X : α → 𝒦)
  [uniformly_bounded X] :
  ∃ (P : α → 𝒦)
  [∀ a, homotopy_category.is_K_projective (P a).val]
  [uniformly_bounded P]
  (f : Π a, P a ⟶ X a),
  (∀ a, homotopy_category.is_quasi_iso (f a)) ∧ ∀ a k, projective ((P a).val.as.X k) :=
begin
  obtain ⟨P,h1,h2,f,h3,h4⟩ := homotopy_category.exists_K_projective_replacement_of_uniformly_bounded_above
    (val ∘ X),
  resetI,
  exact ⟨λ a, ⟨P a⟩, infer_instance, infer_instance, f, h3, h4⟩,
end

open homotopy_category

def replace (X : 𝒦) : 𝒦 := (exists_K_projective_replacement X).some

instance (X : 𝒦) : is_K_projective X.replace.val :=
(exists_K_projective_replacement X).some_spec.some

def π (X : 𝒦) : X.replace ⟶ X :=
(exists_K_projective_replacement X).some_spec.some_spec.some

instance (X : 𝒦) : is_quasi_iso X.π :=
(exists_K_projective_replacement X).some_spec.some_spec.some_spec.1

instance (X : 𝒦) (k : ℤ) : projective (X.replace.val.as.X k) :=
(exists_K_projective_replacement X).some_spec.some_spec.some_spec.2 k

def replace_uniformly {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] : α → bounded_homotopy_category A :=
(exists_uniform_K_projective_replacement X).some

instance is_K_projective_replace_uniformly_apply {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] (a) : homotopy_category.is_K_projective (replace_uniformly X a).val :=
(exists_uniform_K_projective_replacement X).some_spec.some _

def π_uniformly {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] : Π a, replace_uniformly X a ⟶ X a :=
(exists_uniform_K_projective_replacement X).some_spec.some_spec.some_spec.some

instance is_quasi_iso_π_uniformly {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] (a) : homotopy_category.is_quasi_iso (π_uniformly X a) :=
(exists_uniform_K_projective_replacement X).some_spec.some_spec.some_spec.some_spec.1 _

instance uniform_bound_replace_uniformly {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] : uniformly_bounded (replace_uniformly X) :=
(exists_uniform_K_projective_replacement X).some_spec.some_spec.some

def lift {P X Y : 𝒦} [is_K_projective P.val] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  P ⟶ X :=
((hom_K_projective_bijective P.val g).2 f).some

@[simp, reassoc]
lemma lift_lifts {P X Y : 𝒦} [is_K_projective P.val] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  lift f g ≫ g = f :=
((hom_K_projective_bijective P.val g).2 f).some_spec

lemma lift_unique {P X Y : 𝒦} [is_K_projective P.val] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g]
  (e : P ⟶ X) (h : e ≫ g = f) : e = lift f g :=
begin
  apply (hom_K_projective_bijective P.val g).1,
  dsimp,
  erw lift_lifts,
  assumption
end

@[simp]
lemma lift_self {P X : 𝒦} [is_K_projective P.val] (g : P ⟶ X) [is_quasi_iso g] :
  lift g g = 𝟙 _ :=
(lift_unique _ _ _ (by simp)).symm

@[simp]
lemma lift_comp {P X Y : 𝒦} [is_K_projective P.val] (f : P ⟶ X) (g : X ⟶ Y) [is_quasi_iso g] :
  lift (f ≫ g) g = f :=
(lift_unique _ _ _ (by simp)).symm

@[simp, reassoc]
lemma lift_comp_lift_self {P X Y Z : 𝒦} [is_K_projective P.val] [is_K_projective X.val]
  (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] (k : Z ⟶ Y) [is_quasi_iso k] :
  lift f g ≫ lift g k = lift f k :=
lift_unique _ _ _ (by simp)

@[simp, reassoc]
lemma lift_comp_lift_comp {P W X Y Z : 𝒦} [is_K_projective P.val] [is_K_projective X.val]
  (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] (h : Y ⟶ Z) (k : W ⟶ Z) [is_quasi_iso k] :
  lift f g ≫ lift (g ≫ h) k = lift (f ≫ h) k :=
lift_unique _ _ _ (by simp)

@[simp] lemma lift_neg {P X Y : 𝒦} [is_K_projective P.val] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  lift (-f) g = -(lift f g) :=
(lift_unique _ _ _ (by simp)).symm

lemma lift_add {P X Y : 𝒦} [is_K_projective P.val] (f₁ f₂ : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  lift (f₁ + f₂) g = lift f₁ g + lift f₂ g :=
(lift_unique _ _ _ (by simp)).symm

instance is_K_projective_shift (X : 𝒦) [is_K_projective X.val] (m : ℤ) :
  is_K_projective ((category_theory.shift_functor 𝒦 m).obj X).val :=
by exact homotopy_category.is_K_projective_shift X.val m -- strange?

instance {X Y : 𝒦} (g : X ⟶ Y) [is_quasi_iso g] (m : ℤ) :
  is_quasi_iso ((category_theory.shift_functor 𝒦 m).map g) :=
homotopy_category.is_quasi_iso_shift _ _ _ _

lemma shift_functor_map_lift
  {P X Y : 𝒦} [is_K_projective P.val] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] (m : ℤ) :
  (category_theory.shift_functor 𝒦 m).map (lift f g) =
    lift ((category_theory.shift_functor 𝒦 m).map f) ((category_theory.shift_functor 𝒦 m).map g) :=
begin
  apply lift_unique,
  simp only [←category_theory.functor.map_comp, lift_lifts],
end

lemma lift_ext {P X Y : 𝒦} [is_K_projective P.val] (g : X ⟶ Y) [is_quasi_iso g]
  (a b : P ⟶ X) (h : a ≫ g = b ≫ g) : a = b :=
(hom_K_projective_bijective P.val g).1 h

@[simps]
def replace_triangle (T : triangle 𝒦) : triangle 𝒦 :=
{ obj₁ := T.obj₁.replace,
  obj₂ := T.obj₂.replace,
  obj₃ := T.obj₃.replace,
  mor₁ := lift (T.obj₁.π ≫ T.mor₁) T.obj₂.π,
  mor₂ := lift (T.obj₂.π ≫ T.mor₂) T.obj₃.π,
  mor₃ := begin
    have h : is_quasi_iso (T.obj₁.π⟦(1 : ℤ)⟧') := infer_instance,
    exact @lift _ _ _ _ _ _ _ _ (T.obj₃.π ≫ T.mor₃) (T.obj₁.π⟦(1 : ℤ)⟧') h, -- What?
  end }

lemma distinguished_replace_triangle (T : triangle 𝒦) (hT : T ∈ dist_triang 𝒦) :
  replace_triangle T ∈ dist_triang 𝒦 :=
begin
  let S := replace_triangle T,
  change S ∈ _,
  obtain ⟨Z,g,h,hW⟩ := pretriangulated.distinguished_cocone_triangle _ _ S.mor₁,
  let W := triangle.mk (bounded_homotopy_category A) S.mor₁ g h,
  change W ∈ _ at hW,
  have hWT : W.mor₁ ≫ T.obj₂.π = T.obj₁.π ≫ T.mor₁ := _,
  obtain ⟨q,sq2,sq3⟩ := pretriangulated.complete_distinguished_triangle_morphism _ _ hW hT
    T.obj₁.π T.obj₂.π hWT,
  let r : W ⟶ T := ⟨T.obj₁.π, T.obj₂.π, q, hWT, sq2, sq3⟩,
  let W' := (triangle.mk (homotopy_category _ _) W.mor₁ W.mor₂ W.mor₃),
  let T' := (triangle.mk (homotopy_category _ _) T.mor₁ T.mor₂ T.mor₃),
  let r' : W' ⟶ T' := ⟨T.obj₁.π, T.obj₂.π, q, hWT, sq2, sq3⟩,
  haveI : is_quasi_iso r.hom₃, { exact is_quasi_iso_of_triangle W' T' hW hT r' },
  haveI : is_K_projective W.obj₃.val,
  by asyncI
  { haveI : is_K_projective W'.obj₁ := show is_K_projective T.obj₁.replace.val, by apply_instance,
    haveI : is_K_projective W'.obj₂ := show is_K_projective T.obj₂.replace.val, by apply_instance,
    exact homotopy_category.is_K_projective_of_triangle W' hW },
  haveI : is_K_projective S.obj₁.val := show is_K_projective T.obj₁.replace.val, by apply_instance,
  haveI : is_K_projective S.obj₂.val := show is_K_projective T.obj₂.replace.val, by apply_instance,
  haveI : is_K_projective S.obj₃.val := show is_K_projective T.obj₃.replace.val, by apply_instance,
  apply mem_distinguished_of_iso _ hW,
  refine ⟨⟨𝟙 _,𝟙 _, lift q T.obj₃.π, _, _, _⟩,⟨𝟙 _,𝟙 _, lift T.obj₃.π q, _,_,_⟩,_,_⟩,
  asyncI
  { dsimp, rw [category.comp_id, category.id_comp], },
  asyncI
  { dsimp [S, replace_triangle],
    rw category.id_comp,
    apply lift_unique,
    erw [category.assoc, lift_lifts], exact sq2, },
  asyncI
  { dsimp [S, replace_triangle],
    rw [category_theory.functor.map_id, category.comp_id],
    haveI : is_quasi_iso
      ((category_theory.shift_functor (bounded_homotopy_category A) (1 : ℤ)).map T.obj₁.π),
    { show is_quasi_iso (T.obj₁.π⟦(1 : ℤ)⟧'), apply_instance }, -- strange.
    apply lift_ext (T.obj₁.π⟦(1 : ℤ)⟧'),
    erw [category.assoc, lift_lifts, lift_lifts_assoc],
    exact sq3,
    assumption },
  asyncI
  { dsimp, rw [category.id_comp, category.comp_id] },
  asyncI
  { dsimp [S, replace_triangle],
    rw category.id_comp,
    apply lift_ext q,
    erw [category.assoc, lift_lifts, lift_lifts, sq2],
    assumption },
  asyncI
  { dsimp [S, replace_triangle],
    rw [category_theory.functor.map_id, category.comp_id],
    haveI : is_quasi_iso
      ((category_theory.shift_functor (bounded_homotopy_category A) (1 : ℤ)).map T.obj₁.π),
    { show is_quasi_iso (T.obj₁.π⟦(1 : ℤ)⟧'), apply_instance }, -- strange.
    apply lift_ext (T.obj₁.π⟦(1 : ℤ)⟧'),
    erw [category.assoc, lift_lifts, sq3, lift_lifts_assoc],
    assumption },
  asyncI
  { ext; dsimp, rw category.id_comp, rw category.id_comp,
    apply lift_ext q, erw [category.assoc, lift_lifts, lift_lifts, category.id_comp],
    assumption },
  asyncI
  { ext; dsimp, rw category.id_comp, rw category.id_comp,
    apply lift_ext T.obj₃.π, erw [category.assoc, lift_lifts, lift_lifts, category.id_comp],
    assumption },
  asyncI
  { dsimp [W, S, replace_triangle],
    rw lift_lifts },
end

@[simps]
def Ext0 : 𝒦ᵒᵖ ⥤ 𝒦 ⥤ Ab :=
{ obj := λ X, preadditive_yoneda.flip.obj (opposite.op $ X.unop.replace),
  map := λ X₁ X₂ f, preadditive_yoneda.flip.map (lift (X₂.unop.π ≫ f.unop) X₁.unop.π).op,
  map_id' := by asyncI {
    intros X,
    ext Y e,
    dsimp [preadditive_yoneda, preadditive_yoneda_obj],
    change _ ≫ e = e,
    simp only [category.comp_id, id_apply],
    convert category.id_comp _,
    symmetry,
    apply lift_unique,
    simp, },
  map_comp' := by asyncI {
    intros X₁ X₂ X₃ f g,
    ext Y e,
    dsimp,
    simp only [comp_apply, linear_map.to_add_monoid_hom_coe,
      preadditive_yoneda_obj_map_apply, quiver.hom.unop_op],
    change _ ≫ e = _ ≫ _ ≫ e,
    conv_rhs { rw ← category.assoc },
    congr' 1,
    symmetry,
    apply lift_unique,
    simp } }
.

def Ext (i : ℤ) : 𝒦ᵒᵖ ⥤ 𝒦 ⥤ Ab :=
Ext0 ⋙ (whiskering_left _ _ _).obj (shift_functor _ i)

-- why is this so slow?
-- DT: squeezing the simps made it very fast!
@[simps]
def replacement_iso (P₁ P₂ X : 𝒦) [is_K_projective P₁.val] [is_K_projective P₂.val]
  (f₁ : P₁ ⟶ X) (f₂ : P₂ ⟶ X) [is_quasi_iso f₁] [is_quasi_iso f₂] : P₁ ≅ P₂ :=
{ hom         := lift f₁ f₂,
  inv         := lift f₂ f₁,
  hom_inv_id' := by asyncI {
    have : 𝟙 P₁ = lift f₁ f₁,
    { apply lift_unique, simp only [category.id_comp] },
    rw this,
    apply lift_unique,
    simp only [category.assoc, lift_lifts], },
  inv_hom_id' := by asyncI {
    have : 𝟙 P₂ = lift f₂ f₂,
    { apply lift_unique, simp only [category.id_comp] },
      rw this,
    apply lift_unique,
    simp only [category.assoc, lift_lifts], } }
.

@[simps]
def Ext_iso
  (i : ℤ) (P X Y : 𝒦) [is_K_projective P.val]
  (f : P ⟶ X) [is_quasi_iso f] :
  ((Ext i).obj (opposite.op X)).obj Y ≅ AddCommGroup.of (P ⟶ Y⟦i⟧) :=
(preadditive_yoneda.obj (Y⟦i⟧)).map_iso (replacement_iso P X.replace X f X.π).op

instance ext_additive (i : ℤ) (X : 𝒦) : functor.additive ((Ext i).obj (opposite.op X)) :=
begin
  refine ⟨_⟩,
  intros X Y f g,
  ext h,
  dsimp [Ext, preadditive_yoneda],
  rw [(category_theory.shift_functor 𝒦 i).map_add, preadditive.comp_add],
end

instance ext_additive' (i : ℤ) (X : 𝒦) : functor.additive ((Ext i).flip.obj X).right_op :=
begin
  refine ⟨_⟩,
  intros X Y f g,
  dsimp [Ext, preadditive_yoneda],
  rw ← op_add,
  congr' 1,
  ext h,
  dsimp,
  rw ← preadditive.add_comp,
  congr' 1,
  symmetry,
  apply lift_unique,
  simp only [preadditive.add_comp, lift_lifts, preadditive.comp_add],
end .

def _root_.category_theory.adjunction.yoneda_whiskering_left
  {C D : Type*} [category C] [category D] {F : C ⥤ D}
  {G : D ⥤ C} (adj : F ⊣ G) :
  yoneda ⋙ ((whiskering_left _ _ _).obj F.op) ≅ G ⋙ yoneda :=
begin
  fapply nat_iso.of_components,
  { intro Y,
    fapply nat_iso.of_components,
    { intro X, exact (adj.hom_equiv (opposite.unop X) Y).to_iso },
    { intros X₁ X₂ f, ext g, exact adj.hom_equiv_naturality_left f.unop g } },
  { intros Y₁ Y₂ f, ext X g, exact adj.hom_equiv_naturality_right g f }
end

def _root_.category_theory.adjunction.preadditive_yoneda_whiskering_left
  {C D : Type*} [category C] [category D] [preadditive C] [preadditive D] {F : C ⥤ D}
  {G : D ⥤ C} (adj : F ⊣ G) [functor.additive G] :
  preadditive_yoneda ⋙ ((whiskering_left _ _ _).obj F.op) ≅ G ⋙ preadditive_yoneda :=
begin
  fapply nat_iso.of_components,
  { intro Y,
    fapply nat_iso.of_components,
    { intro X,
      refine add_equiv_iso_AddCommGroup_iso.hom
        { map_add' := _, ..(adj.hom_equiv (opposite.unop X) Y) },
      intros f g, simp },
    { intros X₁ X₂ f, ext g, exact adj.hom_equiv_naturality_left f.unop g } },
  { intros Y₁ Y₂ f, ext X g, exact adj.hom_equiv_naturality_right g f }
end
.

end enough_projectives

instance shift_equiv_symm_inverse_additive (i : ℤ) :
  (shift_equiv (bounded_homotopy_category A) i).symm.inverse.additive :=
show (category_theory.shift_functor (bounded_homotopy_category A) (i)).additive, by apply_instance

instance shift_equiv_inverse_additive (i : ℤ) :
  (shift_equiv (bounded_homotopy_category A) i).inverse.additive :=
show (category_theory.shift_functor (bounded_homotopy_category A) (-i)).additive, by apply_instance

def hom_shift_right_iso (X : 𝒦) (i : ℤ) :
  category_theory.shift_functor 𝒦 i ⋙ preadditive_yoneda.flip.obj (opposite.op X) ≅
  preadditive_yoneda.flip.obj (opposite.op (X⟦-i⟧)) :=
begin
  have := (iso_whisker_right ((shift_equiv (bounded_homotopy_category A) i).symm
  .to_adjunction).preadditive_yoneda_whiskering_left.symm
    ((evaluation _ _).obj $ opposite.op X) : _),
  exact this,
end

def hom_shift_left_iso (X : 𝒦) (i : ℤ) :
  (category_theory.shift_functor 𝒦 i).op ⋙ preadditive_yoneda.obj X ≅
  preadditive_yoneda.obj (X⟦-i⟧) :=
begin
  have := (shift_equiv (bounded_homotopy_category A) i)
  .to_adjunction.preadditive_yoneda_whiskering_left.app X,
  exact this,
end

-- The LES for Ext in the second variable.
instance (i : ℤ) (X : 𝒦) [enough_projectives A] : homological_functor ((Ext i).obj (opposite.op X)) :=
begin
  show homological_functor (category_theory.shift_functor 𝒦 i ⋙ preadditive_yoneda.flip.obj _),
  let E := hom_shift_right_iso X.replace i,
  exact homological_of_nat_iso _ _ E.symm,
end

-- The LES for Ext in the first variable.
-- We need K-projective replacements of triangles for this.
instance (i : ℤ) (X : 𝒦) [enough_projectives A] : homological_functor ((Ext i).flip.obj X).right_op :=
begin
  constructor,
  intros T hT,
  have := homological_functor.cond
    (preadditive_yoneda.obj (X⟦i⟧)).right_op
    (replace_triangle T)
    (distinguished_replace_triangle _ hT),
  exact this,
end

instance lift_is_iso
  [enough_projectives A] (X Y X' Y' : 𝒦)
  (f : X ⟶ Y) (πX : X' ⟶ X) (πY : Y' ⟶ Y)
  [homotopy_category.is_quasi_iso f]
  [homotopy_category.is_quasi_iso πX]
  [homotopy_category.is_quasi_iso πY]
  [homotopy_category.is_K_projective X'.val]
  [homotopy_category.is_K_projective Y'.val] :
  is_iso (lift (πX ≫ f) πY) :=
begin
  use lift πY (πX ≫ f),
  split,
  { apply lift_ext (πX ≫ f), simp, apply_instance },
  { apply lift_ext πY, simp, apply_instance }
end

@[simp]
lemma inv_lift
  [enough_projectives A] (X Y X' Y' : 𝒦)
  (f : X ⟶ Y) (πX : X' ⟶ X) (πY : Y' ⟶ Y)
  [homotopy_category.is_quasi_iso f]
  [homotopy_category.is_quasi_iso πX]
  [homotopy_category.is_quasi_iso πY]
  [homotopy_category.is_K_projective X'.val]
  [homotopy_category.is_K_projective Y'.val] :
  inv (lift (πX ≫ f) πY) = lift πY (πX ≫ f) :=
begin
  apply lift_unique, rw is_iso.inv_comp_eq, simp,
end

instance is_iso_Ext_flip_obj_map_of_is_quasi_iso [enough_projectives A] (i : ℤ)
  (X X' Y : 𝒦)
  (f : X ⟶ X') [homotopy_category.is_quasi_iso f] :
  is_iso (((Ext i).flip.obj Y).map f.op) :=
begin
  let e := (preadditive_yoneda.obj (Y⟦i⟧)).map (lift (X.π ≫ f) X'.π).op,
  change is_iso e,
  apply functor.map_is_iso,
end

end bounded_homotopy_category

variable [enough_projectives A]

def Ext' (i : ℤ) : Aᵒᵖ ⥤ A ⥤ Ab :=
(bounded_homotopy_category.single A 0).op ⋙
  (bounded_homotopy_category.single A 0 ⋙ (bounded_homotopy_category.Ext i).flip).flip
