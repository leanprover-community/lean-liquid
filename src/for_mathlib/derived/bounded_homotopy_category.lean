
import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import for_mathlib.derived.homological
import for_mathlib.derived.lemmas
import category_theory.abelian.projective
import for_mathlib.homology
import for_mathlib.snake_lemma3
import for_mathlib.les_homology
import for_mathlib.exact_seq3
import for_mathlib.triangle_shift
import for_mathlib.homology_iso
import for_mathlib.projective_replacement

noncomputable theory

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

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

end bounded_homotopy_category
