import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import for_mathlib.derived.homological
import for_mathlib.derived.bounded_homotopy_category
import category_theory.abelian.projective
import for_mathlib.homology
import for_mathlib.snake_lemma3
import for_mathlib.les_homology
import for_mathlib.exact_seq3
import for_mathlib.triangle_shift
import for_mathlib.homology_iso
import for_mathlib.projective_replacement
-- import for_mathlib.arrow_preadditive

noncomputable theory

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

namespace bounded_homotopy_category

local notation `𝒦` := bounded_homotopy_category A

variable [enough_projectives A]

-- Main theorem about existence of K-projective replacements.
-- Perhaps all we need is this for bounded complexes, in which case we should
-- add an additional typeclass parameter here.
theorem exists_K_projective_replacement (X : 𝒦) :
  ∃ (P : 𝒦) [homotopy_category.is_K_projective P.val] (f : P ⟶ X),
  homotopy_category.is_quasi_iso f :=
begin
  obtain ⟨P,h1,h2,f,h3⟩ :=
    homotopy_category.exists_K_projective_replacement_of_bounded X.val,
  resetI,

  exact ⟨⟨P⟩, h1, f, h3⟩,
end

open homotopy_category

def replace (X : 𝒦) : 𝒦 := (exists_K_projective_replacement X).some

instance (X : 𝒦) : is_K_projective X.replace.val :=
(exists_K_projective_replacement X).some_spec.some

def π (X : 𝒦) : X.replace ⟶ X :=
(exists_K_projective_replacement X).some_spec.some_spec.some

instance (X : 𝒦) : is_quasi_iso X.π :=
(exists_K_projective_replacement X).some_spec.some_spec.some_spec

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

lemma lift_ext {P X Y : 𝒦} [is_K_projective P.val] (g : X ⟶ Y) [is_quasi_iso g]
  (a b : P ⟶ X) (h : a ≫ g = b ≫ g) : a = b :=
(hom_K_projective_bijective P.val g).1 h

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
  { haveI : is_K_projective W'.obj₁ := show is_K_projective T.obj₁.replace.val, by apply_instance,
    haveI : is_K_projective W'.obj₂ := show is_K_projective T.obj₂.replace.val, by apply_instance,
    exact homotopy_category.is_K_projective_of_triangle W' hW },
  haveI : is_K_projective S.obj₁.val := show is_K_projective T.obj₁.replace.val, by apply_instance,
  haveI : is_K_projective S.obj₂.val := show is_K_projective T.obj₂.replace.val, by apply_instance,
  haveI : is_K_projective S.obj₃.val := show is_K_projective T.obj₃.replace.val, by apply_instance,
  apply mem_distinguished_of_iso _ hW,
  refine ⟨⟨𝟙 _,𝟙 _, lift q T.obj₃.π, _, _, _⟩,⟨𝟙 _,𝟙 _, lift T.obj₃.π q, _,_,_⟩,_,_⟩,
  { dsimp, rw [category.comp_id, category.id_comp], },
  { dsimp [S, replace_triangle],
    rw category.id_comp,
    apply lift_unique,
    erw [category.assoc, lift_lifts], exact sq2, },
  { dsimp [S, replace_triangle],
    rw [category_theory.functor.map_id, category.comp_id],
    haveI : is_quasi_iso
      ((category_theory.shift_functor (bounded_homotopy_category A) (1 : ℤ)).map T.obj₁.π),
    { show is_quasi_iso (T.obj₁.π⟦(1 : ℤ)⟧'), apply_instance }, -- strange.
    apply lift_ext (T.obj₁.π⟦(1 : ℤ)⟧'),
    erw [category.assoc, lift_lifts, lift_lifts_assoc],
    exact sq3,
    assumption },
  { dsimp, rw [category.id_comp, category.comp_id] },
  { dsimp [S, replace_triangle],
    rw category.id_comp,
    apply lift_ext q,
    erw [category.assoc, lift_lifts, lift_lifts, sq2],
    assumption },
  { dsimp [S, replace_triangle],
    rw [category_theory.functor.map_id, category.comp_id],
    haveI : is_quasi_iso
      ((category_theory.shift_functor (bounded_homotopy_category A) (1 : ℤ)).map T.obj₁.π),
    { show is_quasi_iso (T.obj₁.π⟦(1 : ℤ)⟧'), apply_instance }, -- strange.
    apply lift_ext (T.obj₁.π⟦(1 : ℤ)⟧'),
    erw [category.assoc, lift_lifts, sq3, lift_lifts_assoc],
    assumption },
  { ext; dsimp, rw category.id_comp, rw category.id_comp,
    apply lift_ext q, erw [category.assoc, lift_lifts, lift_lifts, category.id_comp],
    assumption },
  { ext; dsimp, rw category.id_comp, rw category.id_comp,
    apply lift_ext T.obj₃.π, erw [category.assoc, lift_lifts, lift_lifts, category.id_comp],
    assumption },
  { dsimp [W, S, replace_triangle],
    rw lift_lifts },
end

@[simps]
def Ext0 : 𝒦ᵒᵖ ⥤ 𝒦 ⥤ Ab :=
{ obj := λ X, preadditive_yoneda.flip.obj (opposite.op $ X.unop.replace),
  map := λ X₁ X₂ f, preadditive_yoneda.flip.map (lift (X₂.unop.π ≫ f.unop) X₁.unop.π).op,
  map_id' := begin
    intros X,
    ext Y e,
    dsimp [preadditive_yoneda, preadditive_yoneda_obj],
    change _ ≫ e = e,
    simp only [category.comp_id, id_apply],
    convert category.id_comp _,
    symmetry,
    apply lift_unique,
    simp,
  end,
  map_comp' := begin
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
    simp,
  end } .

def Ext (i : ℤ) : 𝒦ᵒᵖ ⥤ 𝒦 ⥤ Ab :=
Ext0 ⋙ (whiskering_left _ _ _).obj (shift_functor _ i)

-- why is this so slow?
-- DT: squeezing the simps made it very fast!
@[simps]
def replacement_iso (P₁ P₂ X : 𝒦) [is_K_projective P₁.val] [is_K_projective P₂.val]
  (f₁ : P₁ ⟶ X) (f₂ : P₂ ⟶ X) [is_quasi_iso f₁] [is_quasi_iso f₂] : P₁ ≅ P₂ :=
{ hom         := lift f₁ f₂,
  inv         := lift f₂ f₁,
  hom_inv_id' := begin
    have : 𝟙 P₁ = lift f₁ f₁,
    { apply lift_unique, simp only [category.id_comp] },
    rw this,
    apply lift_unique,
    simp only [category.assoc, lift_lifts],
  end,
  inv_hom_id' := begin
    have : 𝟙 P₂ = lift f₂ f₂,
    { apply lift_unique, simp only [category.id_comp] },
      rw this,
    apply lift_unique,
    simp only [category.assoc, lift_lifts],
  end } .

@[simps]
def Ext_iso
  (i : ℤ) (P X Y : 𝒦) [is_K_projective P.val]
  (f : P ⟶ X) [is_quasi_iso f] :
  ((Ext i).obj (opposite.op X)).obj Y ≅ AddCommGroup.of (P ⟶ Y⟦i⟧) :=
(preadditive_yoneda.obj (Y⟦i⟧)).map_iso (replacement_iso _ _ _ f X.π).op

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

def hom_shift_right_iso (X : 𝒦) (i j : ℤ) (h : i + j = 0) :
  category_theory.shift_functor 𝒦 i ⋙ preadditive_yoneda.flip.obj (opposite.op X) ≅
  preadditive_yoneda.flip.obj (opposite.op (X⟦-i⟧)) := sorry

def hom_shift_left_iso (X : 𝒦) (i j : ℤ) (h : i + j = 0) :
  (category_theory.shift_functor 𝒦 i).op ⋙ preadditive_yoneda.obj X ≅
  preadditive_yoneda.obj (X⟦j⟧) := sorry

-- The LES for Ext in the second variable.
instance (i : ℤ) (X : 𝒦) : homological_functor ((Ext i).obj (opposite.op X)) :=
begin
  show homological_functor (category_theory.shift_functor 𝒦 i ⋙ preadditive_yoneda.flip.obj _),
  let E := hom_shift_right_iso X.replace i (-i) (by simp),
  exact homological_of_nat_iso _ _ E.symm,
end

-- The LES for Ext in the first variable.
-- We need K-projective replacements of triangles for this.
instance (i : ℤ) (X : 𝒦) : homological_functor ((Ext i).flip.obj X).right_op :=
begin
  constructor,
  intros T hT,
  have := homological_functor.cond
    (preadditive_yoneda.obj (X⟦i⟧)).right_op
    (replace_triangle T)
    (distinguished_replace_triangle _ hT),
  exact this,
end

-- Move this
@[simps]
def _root_.homotopy_category.single (i : ℤ) : A ⥤ homotopy_category A (complex_shape.up ℤ) :=
homological_complex.single _ _ i ⋙ homotopy_category.quotient _ _

def single (i : ℤ) : A ⥤ bounded_homotopy_category A :=
{ obj := λ X,
  { val := (homotopy_category.single i).obj X,
    bdd := begin
      use i+1,
      intros j hj,
      dsimp,
      erw if_neg,
      { apply is_zero_zero },
      { exact ((i.lt_iff_add_one_le j).mpr hj).ne' }
    end },
  map := λ X Y f, (homotopy_category.single i).map f,
  map_id' := λ X, (homotopy_category.single i).map_id _,
  map_comp' := λ X Y Z f g, (homotopy_category.single i).map_comp f g }

end bounded_homotopy_category

variable [enough_projectives A]

def Ext' (i : ℤ) : Aᵒᵖ ⥤ A ⥤ Ab :=
(bounded_homotopy_category.single 0).op ⋙
  (bounded_homotopy_category.single 0 ⋙ (bounded_homotopy_category.Ext i).flip).flip
