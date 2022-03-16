import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import for_mathlib.derived.homological
import for_mathlib.derived.defs
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

namespace homotopy_category

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)
local notation `HH` := homotopy_category.homology_functor A (complex_shape.up ℤ) 0

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

lemma _root_.category_theory.abelian.exact_neg_right (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)
  [h : exact f g] : exact f (-g) :=
begin
  refine preadditive.exact_of_iso_of_exact' f g f (-g) (iso.refl _) (iso.refl _) _ _ _ h,
  { have : (-𝟙 Z) ≫ (-𝟙 Z) = 𝟙 Z,
    { simp only [preadditive.comp_neg, category.comp_id, neg_neg], },
    exact ⟨-𝟙 Z, -𝟙 Z, this, this⟩, },
  { simp only [iso.refl_hom, category.id_comp, category.comp_id], },
  { simp only [preadditive.comp_neg, category.comp_id, iso.refl_hom, category.id_comp], }
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
  apply_with category_theory.abelian.exact_neg_right { instances := ff },
  apply _root_.category_theory.cochain_complex.exact_cone_in_cone_out,
end .

variable (A)

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

instance is_iso_of_is_quasi_iso' {X Y : 𝒦} (f : X ⟶ Y) [h : is_quasi_iso f] (i : ℤ) :
  is_iso ((homotopy_category.homology_functor _ _ 0).map (f⟦i⟧')) :=
begin
  rw ← is_quasi_iso_iff at h,
  apply h,
end

instance is_iso_of_is_quasi_iso {X Y : 𝒦} (f : X ⟶ Y)
  [is_quasi_iso f] (i : ℤ) :
  is_iso ((homotopy_category.homology_functor _ _ i).map f) :=
begin
  apply is_quasi_iso.cond,
end

instance is_quasi_iso_comp_iso {X Y Z : 𝒦} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : is_quasi_iso f] [hg : is_iso g] :
  is_quasi_iso (f ≫ g) :=
{ cond := λ i, by { rw (homology_functor A (complex_shape.up ℤ) i).map_comp, apply_instance, } }

-- Move This
@[simp] lemma is_iso_neg_iff (A : Type*) [category A]
  [preadditive A] (X Y : A) (f : X ⟶ Y) :
  is_iso (-f) ↔ is_iso f :=
begin
  split; rintro ⟨g, hg⟩; refine ⟨⟨-g, _⟩⟩;
  simpa only [preadditive.comp_neg, preadditive.neg_comp, neg_neg] using hg,
end

-- Move This
@[simp] lemma is_iso_neg_one_pow_iff (A : Type*) [category A]
  [preadditive A] (X Y : A) (f : X ⟶ Y) (i : ℤ) :
  is_iso (i.neg_one_pow • f) ↔ is_iso f :=
begin
  induction i using int.induction_on_iff with i,
  { simp only [int.neg_one_pow_neg_zero, one_zsmul] },
  dsimp,
  simp only [int.neg_one_pow_add, int.neg_one_pow_one, mul_neg, mul_one, neg_smul, is_iso_neg_iff],
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
    erw H.map_zsmul,
    rw is_iso_neg_one_pow_iff,
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
      simp only [functor.map_zsmul],
      rw is_iso_neg_one_pow_iff,
      rw hhh,
      apply_with is_iso.comp_is_iso { instances := ff },
      apply_with is_iso.comp_is_iso { instances := ff },
      all_goals { apply_instance <|> assumption } },
    apply is_quasi_iso.cond },
  apply is_zero_of_exact_seq_of_is_iso_of_is_iso _ _ _ _ E,
end

instance is_acyclic_shift (T : 𝒦) [h : is_acyclic T] (i : ℤ) : is_acyclic (T⟦i⟧) :=
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

instance is_quasi_iso_shift (X Y : 𝒦) (f : X ⟶ Y) [is_quasi_iso f] (i : ℤ) :
  is_quasi_iso (f⟦i⟧') :=
begin
  rw ← is_quasi_iso_iff,
  intros j,
  have := (category_theory.shift_functor_add 𝒦 i j).hom.naturality f,
  apply_fun (λ e, (homology_functor _ _ 0).map e) at this,
  simp only [functor.map_comp, functor.comp_map] at this,
  rw ← is_iso.inv_comp_eq at this,
  rw ← this,
  apply is_iso.comp_is_iso,
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
      apply_with homotopy_category.is_acyclic_shift { instances := ff },
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

instance (X : 𝒦) [is_bounded_above X] (i : ℤ) : is_bounded_above (X⟦i⟧) :=
begin
  obtain ⟨a,ha⟩ := is_bounded_above.cond X,
  use a - i,
  intros j hj,
  apply ha,
  linarith
end

lemma is_K_projective_of_iso (P Q : 𝒦) [is_K_projective P] (e : P ≅ Q) : is_K_projective Q :=
begin
  constructor,
  introsI Y _ f,
  apply_fun (λ q, e.hom ≫ q),
  dsimp,
  rw comp_zero,
  apply is_K_projective.cond,
  intros a b h,
  apply_fun (λ q, e.inv ≫ q) at h,
  simpa using h,
end

instance (P : 𝒦) [is_K_projective P] (i : ℤ) : is_K_projective (P⟦i⟧) :=
begin
  constructor,
  introsI Y _ f,
  let e := (shift_functor_comp_shift_functor_neg _ i).app P,
  dsimp at e,
  haveI : is_K_projective (P⟦i⟧⟦-i⟧) := is_K_projective_of_iso _ _ e.symm,
  apply (category_theory.shift_functor 𝒦 (-i)).map_injective,
  simp,
  apply is_K_projective.cond,
end

lemma is_quasi_iso_of_triangle
  (T₁ T₂ : triangle 𝒦)
  (h₁ : T₁ ∈ dist_triang 𝒦)
  (h₂ : T₂ ∈ dist_triang 𝒦)
  (f : T₁ ⟶ T₂)
  [is_quasi_iso f.hom₁]
  [is_quasi_iso f.hom₂] :
  is_quasi_iso f.hom₃ :=
begin
  -- Another application of the five lemma...
  let H : 𝒦 ⥤ _ := homotopy_category.homology_functor _ _ 0,
  rw ← is_quasi_iso_iff,
  intros i,
  let S₁ := T₁⟦i⟧,
  let S₂ := T₂⟦i⟧,
  let g : S₁ ⟶ S₂ := f⟦i⟧',
  haveI : exact (H.map S₁.mor₁) (H.map S₁.mor₂),
  { apply homological_functor.cond,
    apply pretriangulated.shift_of_dist_triangle,
    assumption },
  haveI : exact (H.map S₁.mor₂) (H.map S₁.mor₃),
  { apply homological_functor.cond H S₁.rotate,
    apply pretriangulated.rot_of_dist_triangle,
    apply pretriangulated.shift_of_dist_triangle,
    assumption },
  haveI : exact (H.map S₁.mor₃) (H.map S₁.rotate.mor₃),
  { apply homological_functor.cond H S₁.rotate.rotate,
    apply pretriangulated.rot_of_dist_triangle,
    apply pretriangulated.rot_of_dist_triangle,
    apply pretriangulated.shift_of_dist_triangle,
    assumption },
  haveI : exact (H.map S₂.mor₁) (H.map S₂.mor₂),
  { apply homological_functor.cond,
    apply pretriangulated.shift_of_dist_triangle,
    assumption },
  haveI : exact (H.map S₂.mor₂) (H.map S₂.mor₃),
  { apply homological_functor.cond H S₂.rotate,
    apply pretriangulated.rot_of_dist_triangle,
    apply pretriangulated.shift_of_dist_triangle,
    assumption },
  haveI : exact (H.map S₂.mor₃) (H.map S₂.rotate.mor₃),
  { apply homological_functor.cond H S₂.rotate.rotate,
    apply pretriangulated.rot_of_dist_triangle,
    apply pretriangulated.rot_of_dist_triangle,
    apply pretriangulated.shift_of_dist_triangle,
    assumption },
  haveI : is_iso (H.map g.hom₁),
  { change is_iso (H.map (f.hom₁⟦i⟧')),
    apply_instance },
  haveI : is_iso (H.map g.hom₂),
  { change is_iso (H.map (f.hom₂⟦i⟧')),
    apply_instance },
  haveI : is_iso (H.map (g.hom₁⟦(1 : ℤ)⟧')),
  { change is_iso (H.map (f.hom₁⟦i⟧'⟦(1 :ℤ)⟧')),
    have := (category_theory.shift_functor_add 𝒦 i 1).hom.naturality f.hom₁,
    apply_fun (λ e, H.map e) at this,
    simp only [H.map_comp, functor.comp_map] at this,
    rw ← is_iso.inv_comp_eq at this,
    rw ← this,
    apply is_iso.comp_is_iso },
  haveI : is_iso (H.map (g.hom₂⟦(1 : ℤ)⟧')),
  { change is_iso (H.map (f.hom₂⟦i⟧'⟦(1 :ℤ)⟧')),
    have := (category_theory.shift_functor_add 𝒦 i 1).hom.naturality f.hom₂,
    apply_fun (λ e, H.map e) at this,
    simp only [H.map_comp, functor.comp_map] at this,
    rw ← is_iso.inv_comp_eq at this,
    rw ← this,
    apply is_iso.comp_is_iso },
  refine @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso A _ _
    (H.obj S₁.obj₁) (H.obj S₁.obj₂) (H.obj S₁.obj₃) (H.obj (S₁.obj₁⟦(1 : ℤ)⟧))
    (H.obj S₂.obj₁) (H.obj S₂.obj₂) (H.obj S₂.obj₃) (H.obj (S₂.obj₁⟦(1 : ℤ)⟧))
    (H.map S₁.mor₁) (H.map S₁.mor₂) (H.map S₁.mor₃)
    (H.map S₂.mor₁) (H.map S₂.mor₂) (H.map S₂.mor₃)
    (H.map g.hom₁) (H.map g.hom₂) (H.map g.hom₃) (H.map (g.hom₁⟦(1 : ℤ)⟧'))
    _ _ _
    (H.obj (S₁.obj₂⟦(1 : ℤ)⟧))
    (H.obj (S₂.obj₂⟦(1 : ℤ)⟧))
    (H.map (S₁.rotate.mor₃))
    (H.map (S₂.rotate.mor₃))
    (H.map (g.hom₂⟦(1 : ℤ)⟧')) _ _ _ _ _ _ _ _ _ _ _,
  { simp only [← H.map_comp, g.comm₁] },
  { simp only [← H.map_comp, g.comm₂] },
  { simp only [← H.map_comp, g.comm₃] },
  { simp only [← functor.map_comp],
    congr' 1,
    dsimp,
    simp only [preadditive.comp_neg, preadditive.neg_comp, neg_inj, ← functor.map_comp, f.comm₁,
      preadditive.zsmul_comp, preadditive.comp_zsmul] },
end

lemma is_K_projective_of_triangle (T : triangle 𝒦) (hT : T ∈ dist_triang 𝒦)
  [is_K_projective T.obj₁] [is_K_projective T.obj₂] : is_K_projective T.obj₃ :=
begin
  constructor,
  introsI Y _ f,
  let H : 𝒦 ⥤ Abᵒᵖ := (preadditive_yoneda.obj Y).right_op,
  haveI : homological_functor H := infer_instance, -- sanity check
  have e := homological_functor.cond H T.rotate
    (rotate_mem_distinguished_triangles _ hT),
  dsimp [H] at e,
  let a := _, let b := _, change exact a b at e, have e' : exact b.unop a.unop,
  { resetI, apply_instance },
  dsimp at e',
  rw AddCommGroup.exact_iff at e',
  let a' := _, let b' := _, change add_monoid_hom.range a' = add_monoid_hom.ker b' at e',
  have : f ∈ b'.ker,
  { change _  ≫ _ = 0,
    apply_with is_K_projective.cond { instances := ff },
    dsimp,
    apply_instance,
    apply_instance },
  rw ← e' at this,
  obtain ⟨g,hg⟩ := this,
  dsimp at hg,
  rw ← hg,
  have : g = 0,
  { apply is_K_projective.cond },
  simp [this],
end

variable [enough_projectives A]

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
