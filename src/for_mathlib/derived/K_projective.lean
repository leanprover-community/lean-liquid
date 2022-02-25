import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import for_mathlib.derived.homological
import category_theory.abelian.projective
import for_mathlib.homology
import for_mathlib.snake_lemma3
import for_mathlib.les_homology
import for_mathlib.exact_seq3
import for_mathlib.triangle_shift
import for_mathlib.homology_iso
import for_mathlib.projective_replacement
-- import for_mathlib.arrow_preadditive

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

namespace homotopy_category
universes v u
variables {A : Type u} [category.{v} A] [abelian A]

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)
local notation `HH` := homotopy_category.homology_functor A (complex_shape.up ℤ) 0

class is_acyclic (X : 𝒦) : Prop :=
(cond [] : ∀ i, is_zero ((homotopy_category.homology_functor _ _ i).obj X))

lemma is_acyclic_of_iso {X Y : 𝒦} (e : X ≅ Y) [is_acyclic X] : is_acyclic Y :=
begin
  constructor,
  intros i,
  let e' : (homology_functor A (complex_shape.up ℤ) i).obj X ≅
    (homology_functor A (complex_shape.up ℤ) i).obj Y :=
    functor.map_iso _ e,
  apply is_zero_of_iso_of_zero _ e',
  apply is_acyclic.cond X i,
end

class is_K_projective (X : 𝒦) : Prop :=
(cond : ∀ (Y : 𝒦) [is_acyclic Y] (f : X ⟶ Y), f = 0)

class is_quasi_iso {X Y : 𝒦} (f : X ⟶ Y) : Prop :=
(cond : ∀ i, is_iso ((homotopy_category.homology_functor _ _ i).map f))

-- Move this
instance homology_functor_additive : functor.additive HH := functor.additive.mk $
begin
  rintros X Y ⟨f⟩ ⟨g⟩,
  dsimp [homotopy_category.homology_functor],
  erw ← (_root_.homology_functor _ _ _).map_add,
  refl,
  apply_instance,
end

lemma _root_.category_theory.cochain_complex.exact_cone_in_cone_out
  (X Y : cochain_complex A ℤ) (f : X ⟶ Y) :
  exact ((_root_.homology_functor _ _ 0).map (cone.in f))
    ((_root_.homology_functor _ _ 0).map (cone.out f)) :=
begin
  refine (homological_complex.six_term_exact_seq (cone.in f) (cone.out f) _ 0 1 rfl).pair,
  intro n,
  apply (cone.termwise_split _ _).short_exact,
end

/-
lemma _root_.category_theory.cochain_complex.exact_to_cone_in
  (X Y : cochain_complex A ℤ) (f : X ⟶ Y) :
  exact ((_root_.homology_functor _ _ 0).map f)
    ((_root_.homology_functor _ _ 0).map (cone.in f)) :=
begin
  sorry
end
-/

section

local attribute [instance] abelian.pseudoelement.hom_to_fun
  abelian.pseudoelement.has_zero abelian.pseudoelement.setoid

lemma _root_.category_theory.abelian.exact_of_neg_right (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)
  [h : exact f g] : exact f (-g) :=
begin
  apply abelian.pseudoelement.exact_of_pseudo_exact,
  split,
  intros a,
  rw ← abelian.pseudoelement.comp_apply,
  simp,
  intros b hb,
  apply abelian.pseudoelement.pseudo_exact_of_exact.2 b (_ : g b = 0),
  apply_instance,
  rcases b,
  apply abelian.pseudoelement.apply_eq_zero_of_comp_eq_zero g b.hom,
  erw abelian.pseudoelement.pseudo_zero_iff at hb,
  simpa using hb,
end

end

instance homology_functor_homological : homological_functor HH :=
begin
  apply homological_of_rotate,
  intros T hT,
  erw mem_distinguished_iff_exists_iso_cone at hT,
  obtain ⟨X,Y,f,⟨E⟩⟩ := hT,
  let E' : T.rotate ≅
    ((neg₃_functor (homotopy_category A (complex_shape.up ℤ))).obj (cone.triangleₕ f)).rotate :=
    ⟨E.hom.rotate, E.inv.rotate, _, _⟩,
  rotate,
  { ext; dsimp,
    { change (E.hom ≫ E.inv).hom₂ = _, rw iso.hom_inv_id, refl },
    { change (E.hom ≫ E.inv).hom₃ = _, rw iso.hom_inv_id, refl },
    { simp only [← functor.map_comp],
      change (category_theory.shift_functor 𝒦 (1 : ℤ)).map ((E.hom ≫ E.inv).hom₁) = _,
      rw iso.hom_inv_id, refl } },
  { ext; dsimp,
    { change (E.inv ≫ E.hom).hom₂ = _, rw iso.inv_hom_id, refl },
    { change (E.inv ≫ E.hom).hom₃ = _, rw iso.inv_hom_id, refl },
    { simp only [← functor.map_comp],
      change (category_theory.shift_functor 𝒦 (1 : ℤ)).map ((E.inv ≫ E.hom).hom₁) = _,
      rw iso.inv_hom_id, refl } },
  apply homological_of_exists_aux _ _ _ E'.inv,
  apply_instance,
  dsimp,
  simp only [functor.map_neg],
  apply_with category_theory.abelian.exact_of_neg_right { instances := ff },
  apply _root_.category_theory.cochain_complex.exact_cone_in_cone_out,
end .

variable (A)

noncomputable
def homology_shift_iso (i j : ℤ) :
  category_theory.shift_functor (homotopy_category A (complex_shape.up ℤ)) i ⋙
    homology_functor A (complex_shape.up ℤ) j ≅ homology_functor A (complex_shape.up ℤ) (j+i) :=
nat_iso.of_components (λ (X : 𝒦), homology_shift_obj_iso X.as i j : _)
begin
  intros X Y f,
  rw ← quotient_map_out f,
  dsimp,
  erw homotopy_category.shift_functor_map_quotient,
  rw ← homology_functor_map_factors,
  erw (homology_shift_iso A i j).hom.naturality,
  erw ← homology_functor_map_factors,
  refl
end

noncomputable
def homology_zero_shift_iso (i : ℤ) :
  category_theory.shift_functor (homotopy_category A (complex_shape.up ℤ)) i ⋙
    homology_functor A (complex_shape.up ℤ) 0 ≅ homology_functor A (complex_shape.up ℤ) i :=
homology_shift_iso _ _ _ ≪≫ (eq_to_iso (by rw zero_add))

variable {A}

lemma is_acyclic_iff (X : 𝒦) :
  (∀ (i : ℤ), is_zero ((homotopy_category.homology_functor _ _ 0).obj (X⟦i⟧))) ↔
  is_acyclic X :=
begin
  split,
  { intros h,
    constructor,
    intros i,
    apply is_zero_of_iso_of_zero (h i),
    apply (homology_zero_shift_iso A i).app _ },
  { introsI h i,
    apply is_zero_of_iso_of_zero (is_acyclic.cond _ i),
    apply ((homology_zero_shift_iso A _).app _).symm,
    assumption },
end

lemma is_quasi_iso_iff {X Y : 𝒦} (f : X ⟶ Y) :
  (∀ (i : ℤ), is_iso ((homotopy_category.homology_functor _ _ 0).map (f⟦i⟧'))) ↔
  is_quasi_iso f :=
begin
  split,
  { intros h,
    constructor,
    intros i,
    specialize h i,
    have := (homology_zero_shift_iso A i).hom.naturality f,
    rw ← is_iso.inv_comp_eq at this,
    rw ← this,
    apply_with is_iso.comp_is_iso { instances := ff },
    apply_instance,
    apply_with is_iso.comp_is_iso { instances := ff },
    exact h,
    apply_instance },
  { introsI h i,
    have := (homology_zero_shift_iso A i).hom.naturality f,
    rw ← is_iso.eq_comp_inv at this,
    erw this,
    apply_with is_iso.comp_is_iso { instances := ff },
    apply_with is_iso.comp_is_iso { instances := ff },
    apply_instance,
    apply is_quasi_iso.cond,
    apply_instance }
end

/--
If `A → B → C → A[1]` is a distinguished triangle, and `A → B` is a quasi-isomorphism,
then `C` is acyclic.
-/
lemma is_acyclic_of_dist_triang_of_is_quasi_iso (T : triangle 𝒦) (hT : T ∈ dist_triang 𝒦)
  [h : is_quasi_iso T.mor₁] : is_acyclic T.obj₃ :=
begin
  let H := homology_functor A (complex_shape.up ℤ) 0,
  rw ← is_acyclic_iff,
  intros i,
  let S : triangle 𝒦 := T⟦i⟧,
  have hS : S ∈ dist_triang 𝒦,
  { apply pretriangulated.shift_of_dist_triangle, assumption },
  change is_zero (H.obj (S.obj₃)),
  let E : exact_seq A [H.map S.mor₁, H.map S.mor₂, H.map S.mor₃, H.map (S.rotate.mor₃)],
  { apply exact_seq.cons,
    apply homological_functor.cond H _ hS,
    apply exact_seq.cons,
    apply homological_functor.cond H S.rotate,
    apply rotate_mem_distinguished_triangles _ hS,
    rw ← exact_iff_exact_seq,
    apply homological_functor.cond H S.rotate.rotate,
    apply rotate_mem_distinguished_triangles,
    apply rotate_mem_distinguished_triangles,
    exact hS },
  haveI : is_iso (H.map S.mor₁),
  { have hh := h,
    rw ← is_quasi_iso_iff at h,
    apply h },
  haveI : is_iso (H.map (S.rotate.mor₃)),
  { dsimp [triangle.rotate],
    rw functor.map_neg,
    let f := _, show is_iso (- f),
    suffices : is_iso f,
    { resetI, use (-(inv f)), split, simp, simp },
    let EE : (category_theory.shift_functor 𝒦 i ⋙ category_theory.shift_functor 𝒦 (1 : ℤ)) ⋙ H ≅
      homology_functor _ _ (i + 1),
    { refine iso_whisker_right _ _ ≪≫ homology_zero_shift_iso _ (i + 1),
      refine (shift_functor_add _ _ _).symm },
    suffices : is_iso ((homology_functor _ _ (i+1)).map T.mor₁),
    { have hhh := EE.hom.naturality T.mor₁,
      rw ← is_iso.eq_comp_inv at hhh,
      dsimp only [functor.comp_map] at hhh,
      dsimp [f],
      rw hhh,
      apply_with is_iso.comp_is_iso { instances := ff },
      apply_with is_iso.comp_is_iso { instances := ff },
      all_goals { apply_instance <|> assumption } },
    apply is_quasi_iso.cond },
  apply is_zero_of_exact_seq_of_is_iso_of_is_iso _ _ _ _ E,
end

lemma is_acyclic_shift (T : 𝒦) [h : is_acyclic T] (i : ℤ) : is_acyclic (T⟦i⟧) :=
begin
  rw ← is_acyclic_iff,
  intros j,
  let H := homology_functor A (complex_shape.up ℤ) 0,
  let e : H.obj (T⟦i⟧⟦j⟧) ≅ (homology_functor A (complex_shape.up ℤ) (i+j)).obj T :=
    _ ≪≫ (homology_zero_shift_iso _ (i+j)).app T,
  swap,
  { let e := (iso_whisker_right (shift_functor_add _ i j).symm H).app T,
    refine _ ≪≫ e,
    refine iso.refl _ },
  apply is_zero_of_iso_of_zero _ e.symm,
  apply is_acyclic.cond,
end

lemma hom_K_projective_bijective {X Y : 𝒦} (P : 𝒦) [is_K_projective P]
  (f : X ⟶ Y) [hf : is_quasi_iso f] : function.bijective (λ e : P ⟶ X, e ≫ f) :=
begin
  /-
  Steps:
  1. Complete `f` to a dist triang `X → Y → Z → X[1]`.
  2. Use LES assoc. to `Hom(P,-)`, proved in `for_mathlib/derived/homological.lean`.
  3. Use lemma above + def of K-projective to see that `Hom(P,Z) = 0`.
  -/
  obtain ⟨Z,g,h,hT⟩ := pretriangulated.distinguished_cocone_triangle _ _ f,
  let T := triangle.mk _ f g h,
  change T ∈ _ at hT,
  let H : 𝒦 ⥤ Ab := preadditive_yoneda.flip.obj (opposite.op P),
  have EE : exact_seq Ab [arrow.mk (H.map T.inv_rotate.mor₁), arrow.mk (H.map f), H.map g],
  { apply exact_seq.cons,
    apply homological_functor.cond H T.inv_rotate,
    apply inv_rotate_mem_distinguished_triangles,
    assumption,
    rw ← exact_iff_exact_seq,
    apply homological_functor.cond H T hT },
  split,
  { intros e₁ e₂ hh,
    let ee := (EE.extract 0 2).pair,
    rw AddCommGroup.exact_iff at ee,
    dsimp at hh,
    rw [← sub_eq_zero, ← preadditive.sub_comp] at hh,
    change _ ∈ (H.map f).ker at hh,
    rw ← ee at hh,
    obtain ⟨g,hg⟩ := hh,
    let g' : P ⟶ _ := g,
    haveI : is_acyclic T.inv_rotate.obj₁,
    { change is_acyclic ((T.obj₃)⟦(-1 : ℤ)⟧),
      apply_with is_acyclic_shift { instances := ff },
      haveI : is_quasi_iso T.mor₁ := hf,
      apply is_acyclic_of_dist_triang_of_is_quasi_iso,
      exact hT },
    have : g' = 0,
    { apply is_K_projective.cond },
    change g' ≫ _ = _ at hg,
    rw [this, zero_comp] at hg,
    rw ← sub_eq_zero,
    exact hg.symm },
  { intros q,
    have : q ≫ g = 0,
    { haveI : is_acyclic Z,
      { change is_acyclic T.obj₃,
        apply_with is_acyclic_of_dist_triang_of_is_quasi_iso { instances := ff },
        assumption,
        exact hf },
      apply is_K_projective.cond },
    let ee := (EE.extract 1 3).pair,
    rw AddCommGroup.exact_iff at ee,
    change _ ∈ (H.map g).ker at this,
    rwa ← ee at this }
end

variable [enough_projectives A]
noncomputable theory

lemma exists_K_projective_replacement_of_bounded (X : 𝒦)
  (H : ∃ a, ∀ i, a ≤ i → is_zero (X.as.X i)) :
  ∃ (P : 𝒦) [is_K_projective P] (f : P ⟶ X), is_quasi_iso f :=
begin
  obtain ⟨a, H⟩ := H,
  use projective.replacement X.as a H,
  split,
  { constructor,
    intros Y hY f,
    convert eq_of_homotopy _ _ (projective.null_homotopic_of_projective_to_acyclic f.out a
      (projective.replacement_is_projective X.as a H)
      (projective.replacement_is_bounded X.as a H)
      hY.1),
    simp },
  { use (quotient _ _).map (projective.replacement.hom X.as a H),
    constructor,
    intro i,
    erw ← homology_functor_map_factors,
    apply_instance }
end

-- Main theorem about existence of K-projective replacements.
-- Perhaps all we need is this for bounded complexes, in which case we should
-- add an additional typeclass parameter here.
theorem exists_K_projective_replacement (X : 𝒦) :
  ∃ (P : 𝒦) [is_K_projective P] (f : P ⟶ X), is_quasi_iso f := sorry

def replace (X : 𝒦) : 𝒦 := (exists_K_projective_replacement X).some

instance (X : 𝒦) : is_K_projective X.replace :=
(exists_K_projective_replacement X).some_spec.some

def π (X : 𝒦) : X.replace ⟶ X :=
(exists_K_projective_replacement X).some_spec.some_spec.some

instance (X : 𝒦) : is_quasi_iso X.π :=
(exists_K_projective_replacement X).some_spec.some_spec.some_spec

def lift {P X Y : 𝒦} [is_K_projective P] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  P ⟶ X :=
((hom_K_projective_bijective P g).2 f).some

@[simp, reassoc]
lemma lift_lifts {P X Y : 𝒦} [is_K_projective P] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  lift f g ≫ g = f :=
((hom_K_projective_bijective P g).2 f).some_spec

lemma lift_unique {P X Y : 𝒦} [is_K_projective P] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g]
  (e : P ⟶ X) (h : e ≫ g = f) : e = lift f g :=
begin
  apply (hom_K_projective_bijective P g).1,
  simpa,
end

lemma lift_ext {P X Y : 𝒦} [is_K_projective P] (g : X ⟶ Y) [is_quasi_iso g]
  (a b : P ⟶ X) (h : a ≫ g = b ≫ g) : a = b :=
(hom_K_projective_bijective P g).1 h

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

end homotopy_category
