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

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

namespace homotopy_category

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
(cond [] : ∀ (Y : 𝒦) [is_acyclic Y] (f : X ⟶ Y), f = 0)

class is_quasi_iso {X Y : 𝒦} (f : X ⟶ Y) : Prop :=
(cond [] : ∀ i, is_iso ((homotopy_category.homology_functor _ _ i).map f))

class is_bounded_above (X : 𝒦) : Prop  :=
(cond [] : ∃ a : ℤ, ∀ i, a ≤ i → is_zero (X.as.X i))

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

instance (X : 𝒦) [is_bounded_above X] (i : ℤ) : is_bounded_above (X⟦i⟧) := sorry

instance (P : 𝒦) [is_K_projective P] (i : ℤ) : is_K_projective (P⟦i⟧) := sorry

variable [enough_projectives A]
noncomputable theory

lemma exists_K_projective_replacement_of_bounded (X : 𝒦)
  [is_bounded_above X] :
  ∃ (P : 𝒦) [is_K_projective P] [is_bounded_above P]
    (f : P ⟶ X), is_quasi_iso f :=
begin
  obtain ⟨a, H⟩ := is_bounded_above.cond X,
  use projective.replacement X.as a H,
  refine ⟨_, _, _⟩,
  { constructor,
    intros Y hY f,
    convert eq_of_homotopy _ _ (projective.null_homotopic_of_projective_to_acyclic f.out a
      (projective.replacement_is_projective X.as a H)
      (projective.replacement_is_bounded X.as a H)
      hY.1),
    simp },
  { use a,
    apply projective.replacement_is_bounded },
  { use (quotient _ _).map (projective.replacement.hom X.as a H),
    constructor,
    intro i,
    erw ← homology_functor_map_factors,
    apply_instance }
end

end homotopy_category

variable (A)

structure bounded_homotopy_category :=
(val : homotopy_category A (complex_shape.up ℤ))
[bdd : homotopy_category.is_bounded_above val]

variable {A}

namespace bounded_homotopy_category

instance : category (bounded_homotopy_category A) :=
{ hom := λ X Y, X.val ⟶ Y.val,
  id := λ X, 𝟙 X.val,
  comp := λ X Y Z f g, f ≫ g,
  id_comp' := λ _ _ _, category.id_comp _,
  comp_id' := λ _ _ _, category.comp_id _,
  assoc' := λ _ _ _ _ _ _ _, category.assoc _ _ _ }

local attribute [instance] has_zero_object.has_zero

instance (X : bounded_homotopy_category A) : homotopy_category.is_bounded_above X.val := X.bdd

def of (X : homotopy_category A (complex_shape.up ℤ)) [homotopy_category.is_bounded_above X] :
  bounded_homotopy_category A := ⟨X⟩

instance : has_zero_object (bounded_homotopy_category A) :=
{ zero :=
  { val := 0,
    bdd := ⟨⟨0, λ i _, by apply is_zero_zero ⟩⟩ },
  unique_to := λ X, has_zero_object.unique_to _,
  unique_from := λ X, has_zero_object.unique_from _ }

/-
lemma is_bounded_shift (X : bounded_homotopy_category A) (i : ℤ) :
  ∃ (a : ℤ), ∀ j, a ≤ j → is_zero (X.val⟦i⟧.as.X j) :=
begin
  obtain ⟨a,ha⟩ := X.2,
  use a - i,
  intros j hj,
  apply ha,
  linarith
end
-/

local attribute [instance] endofunctor_monoidal_category
local attribute [reducible] endofunctor_monoidal_category discrete.add_monoidal

instance : has_shift (bounded_homotopy_category A) ℤ :=
has_shift_mk _ _
{ F := λ i,
  { obj := λ X, ⟨X.val⟦(i : ℤ)⟧⟩,
    map := λ X Y f, f⟦i⟧',
    map_id' := λ X, (category_theory.shift_functor _ _).map_id _,
    map_comp' := λ X Y Z f g, (category_theory.shift_functor _ _).map_comp _ _ },
  ε :=
  { hom :=
    { app := λ X, (homotopy_category.shift_ε _).hom.app X.val,
      naturality' := λ _ _ _, (homotopy_category.shift_ε _).hom.naturality _ },
    inv :=
    { app := λ X, (homotopy_category.shift_ε _).inv.app X.val,
      naturality' := λ _ _ _, (homotopy_category.shift_ε _).inv.naturality _ },
    hom_inv_id' := begin
      ext,
      dsimp,
      erw [← nat_trans.comp_app, iso.hom_inv_id],
      refl,
    end,
    inv_hom_id' := begin
      ext,
      dsimp,
      erw [← nat_trans.comp_app, iso.inv_hom_id],
      refl,
    end },
  μ := λ m n,
  { hom :=
    { app := λ X, (homotopy_category.shift_functor_add _ _ _).hom.app X.val,
      naturality' := λ _ _ _, (homotopy_category.shift_functor_add _ _ _).hom.naturality _ },
    inv :=
    { app := λ X, (homotopy_category.shift_functor_add _ _ _).inv.app X.val,
      naturality' := λ _ _ _, (homotopy_category.shift_functor_add _ _ _).inv.naturality _ },
    hom_inv_id' := begin
      ext,
      dsimp,
      erw [← nat_trans.comp_app, iso.hom_inv_id],
      refl,
    end,
    inv_hom_id' := begin
      ext,
      dsimp,
      erw [← nat_trans.comp_app, iso.inv_hom_id],
      refl,
    end },
  associativity := λ m₁ m₂ m₃ X, homotopy_category.has_shift_associativity_aux _ m₁ m₂ m₃ X.val,
  left_unitality := λ n X, homotopy_category.has_shift_left_unitality_aux _ n X.val,
  right_unitality := λ n X, homotopy_category.has_shift_right_unitality_aux _ n X.val } .

instance : preadditive (bounded_homotopy_category A) :=
{ hom_group := λ A B, show add_comm_group (A.val ⟶ B.val), by apply_instance,
  add_comp' := λ P Q R f g h, preadditive.add_comp _ _ _ _ _ _,
  comp_add' := λ P Q R f g h, preadditive.comp_add _ _ _ _ _ _ }

instance shift_functor_additive (i : ℤ) :
  (category_theory.shift_functor (bounded_homotopy_category A) i).additive :=
by constructor

instance : triangulated.pretriangulated (bounded_homotopy_category A) :=
{ distinguished_triangles :=
  { T | triangle.mk (homotopy_category _ _) T.mor₁ T.mor₂ T.mor₃ ∈
    dist_triang (homotopy_category A (complex_shape.up ℤ)) },
  isomorphic_distinguished := begin
    intros T₁ hT₁ T₂ e,
    let S₁ : triangle (homotopy_category _ _) := triangle.mk _ T₁.mor₁ T₁.mor₂ T₁.mor₃,
    let S₂ : triangle (homotopy_category _ _) := triangle.mk _ T₂.mor₁ T₂.mor₂ T₂.mor₃,
    let E : S₂ ≅ S₁ :=
      triangle.iso.of_components
        ⟨e.hom.hom₁,e.inv.hom₁,_,_⟩
        ⟨e.hom.hom₂,e.inv.hom₂,_,_⟩
        ⟨e.hom.hom₃,e.inv.hom₃,_,_⟩
        _ _ _,
    apply pretriangulated.isomorphic_distinguished _ _ _ E,
    apply hT₁,

    { show (e.hom ≫ e.inv).hom₁ = _, rw iso.hom_inv_id, refl },
    { show (e.inv ≫ e.hom).hom₁ = _, rw iso.inv_hom_id, refl },

    { show (e.hom ≫ e.inv).hom₂ = _, rw iso.hom_inv_id, refl },
    { show (e.inv ≫ e.hom).hom₂ = _, rw iso.inv_hom_id, refl },

    { show (e.hom ≫ e.inv).hom₃ = _, rw iso.hom_inv_id, refl },
    { show (e.inv ≫ e.hom).hom₃ = _, rw iso.inv_hom_id, refl },

    { exact e.hom.comm₁ },
    { exact e.hom.comm₂ },
    { exact e.hom.comm₃ }
  end,
  contractible_distinguished := λ X, pretriangulated.contractible_distinguished _,
  distinguished_cocone_triangle := begin
    intros X Y f,
    let T := (neg₃_functor (homotopy_category A (complex_shape.up ℤ))).obj (cone.triangleₕ f.out),
    let E := T.obj₃,
    haveI : homotopy_category.is_bounded_above E,
    { obtain ⟨a,ha⟩ := X.2,
      obtain ⟨b,hb⟩ := Y.2,
      use max (a - 1) b,
      intros i hi,
      apply is_zero_biprod,
      { apply ha, suffices : a - 1 ≤ i, by linarith, apply le_trans _ hi, apply le_max_left },
      { apply hb, apply le_trans _ hi, apply le_max_right } },
    refine ⟨⟨E⟩, T.mor₂, T.mor₃, _⟩,
    { erw homotopy_category.mem_distinguished_iff_exists_iso_cone,
      use [X.val.as, Y.val.as, f.out],
      unfreezingI {
      rcases X with ⟨⟨X⟩,hX⟩,
      rcases Y with ⟨⟨Y⟩,hY⟩,
      constructor,
      refine triangle.iso.of_components
        (iso.refl _) (iso.refl _) (iso.refl _) _ _ _,
      all_goals { dsimp [T], simp } } }
  end,
  rotate_distinguished_triangle := begin
    intros T,
    split,
    { intros hT,
      apply homotopy_category.rotate_mem_distinguished_triangles _ hT },
    { intros hT,
      erw pretriangulated.rotate_distinguished_triangle,
      exact hT }
  end,
  complete_distinguished_triangle_morphism := begin
    intros T₁ T₂ hT₁ hT₂ f g h,
    apply pretriangulated.complete_distinguished_triangle_morphism _ _ hT₁ hT₂ f g h,
  end }

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
@[simps]
def replacement_iso (P₁ P₂ X : 𝒦) [is_K_projective P₁.val] [is_K_projective P₂.val]
  (f₁ : P₁ ⟶ X) (f₂ : P₂ ⟶ X) [is_quasi_iso f₁] [is_quasi_iso f₂] : P₁ ≅ P₂ :=
{ hom := lift f₁ f₂,
  inv := lift f₂ f₁,
  hom_inv_id' := begin
    have : 𝟙 P₁ = lift f₁ f₁,
    { apply lift_unique, simp },
    rw this,
    apply lift_unique, simp,
  end,
  inv_hom_id' := begin
    have : 𝟙 P₂ = lift f₂ f₂,
    { apply lift_unique, simp },
    rw this,
    apply lift_unique, simp
  end } .

@[simps]
def Ext_iso
  (i : ℤ) (P X Y : 𝒦) [is_K_projective P.val]
  (f : P ⟶ X) [is_quasi_iso f] :
  ((Ext i).obj (opposite.op X)).obj Y ≅ AddCommGroup.of (P ⟶ Y⟦i⟧) :=
(preadditive_yoneda.obj (Y⟦i⟧)).map_iso (replacement_iso _ _ _ f X.π).op

-- Move this
@[simps]
def _root_.homotopy_category.single (i : ℤ) : A ⥤ homotopy_category A (complex_shape.up ℤ) :=
homological_complex.single _ _ i ⋙ homotopy_category.quotient _ _

def single (i : ℤ) : A ⥤ bounded_homotopy_category A :=
{ obj := λ X,
  { val := (homotopy_category.single i).obj X,
    property := begin
      use i+1,
      intros j hj,
      dsimp,
      erw if_neg,
      { apply is_zero_zero },
      { linarith }
    end },
  map := λ X Y f, (homotopy_category.single i).map f,
  map_id' := λ X, (homotopy_category.single i).map_id _,
  map_comp' := λ X Y Z f g, (homotopy_category.single i).map_comp f g }

end bounded_homotopy_category

variable [enough_projectives A]

def Ext' (i : ℤ) : Aᵒᵖ ⥤ A ⥤ Ab :=
(bounded_homotopy_category.single 0).op ⋙
  (bounded_homotopy_category.single 0 ⋙ (bounded_homotopy_category.Ext i).flip).flip
