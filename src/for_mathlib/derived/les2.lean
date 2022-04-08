import for_mathlib.derived.lemmas
import for_mathlib.derived.les

open category_theory
open category_theory.limits
open category_theory.triangulated

variables {A : Type*} [category A] [abelian A]

namespace homological_complex
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

noncomputable theory

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)

-- The 5-lemma with no instances... I think this is more convenient to apply in practice.
lemma _root_.category_theory.abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso' :
  ∀ {U B C D A' B' C' D' : A} {f : U ⟶ B} {g : B ⟶ C}
  {h : C ⟶ D} {f' : A' ⟶ B'} {g' : B' ⟶ C'} {h' : C' ⟶ D'} {α : U ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'}
  {δ : D ⟶ D'},
    α ≫ f' = f ≫ β →
    β ≫ g' = g ≫ γ →
    γ ≫ h' = h ≫ δ →
    ∀ {E E' : A} {i : D ⟶ E} {i' : D' ⟶ E'} {ε : E ⟶ E'},
      δ ≫ i' = i ≫ ε →
      exact f g → exact g h → exact h i →  exact f' g' →
      exact g' h' → exact h' i' → is_iso α →  is_iso β →
      is_iso δ → is_iso ε → is_iso γ :=
begin
  intros U B C D A' B' C' D' f g h f' g' h' α β γ δ w1 w2 w3 E E' i i' ε w4,
  intros hfg hgh hhi hf'g' hg'h' hh'i' hα hβ hδ hε, resetI,
  apply abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso w1 w2 w3 w4 hfg hgh hhi hf'g' hg'h' hh'i',
end

theorem is_iso_homology_functor_map (ses : ∀ (i : ℤ), short_exact (f.f i) (g.f i)) :
  is_iso ((homology_functor _ _ 0).map (cone.π f g (λ i, (ses i).exact.w))) :=
begin
  let X' : 𝒦 := (homotopy_category.quotient _ _).obj X,
  let Y' : 𝒦 := (homotopy_category.quotient _ _).obj Y,
  let Z' : 𝒦 := (homotopy_category.quotient _ _).obj Z,
  let f' : X' ⟶ Y' := (homotopy_category.quotient _ _).map f,
  let g' : Y' ⟶ Z' := (homotopy_category.quotient _ _).map g,
  let T : triangle (homotopy_category A (complex_shape.up ℤ)) :=
    (neg₃_functor _).obj (cone.triangleₕ f),
  have hT : T ∈ dist_triang 𝒦,
  { erw homotopy_category.mem_distinguished_iff_exists_iso_cone,
    refine ⟨_, _, f, ⟨iso.refl _⟩⟩ },
  have E1 := five_term_exact_seq' (homotopy_category.homology_functor A (complex_shape.up ℤ) 0)
    T hT,
  have E2 := six_term_exact_seq f g ses 0 1 rfl,
  let EE := homology_shift_iso A 1 0,
  rw zero_add at EE,
  have key := @_root_.category_theory.abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso' _ _ _
    ((homotopy_category.homology_functor _ _ 0).obj T.obj₁)
    ((homotopy_category.homology_functor _ _ 0).obj T.obj₂)
    ((homotopy_category.homology_functor _ _ 0).obj T.obj₃)
    ((homotopy_category.homology_functor _ _ 0).obj (T.obj₁⟦(1 : ℤ)⟧))
    ((homology_functor _ _ 0).obj X)
    ((homology_functor _ _ 0).obj Y)
    ((homology_functor _ _ 0).obj Z)
    ((homology_functor _ _ 1).obj X)
    ((homotopy_category.homology_functor _ _ 0).map T.mor₁)
    ((homotopy_category.homology_functor _ _ 0).map T.mor₂)
    ((homotopy_category.homology_functor _ _ 0).map T.mor₃)
    ((homology_functor _ _ 0).map f)
    ((homology_functor _ _ 0).map g)
    (δ f g ses 0 1 rfl)
    (𝟙 _) (𝟙 _)
    ((homology_functor _ _ 0).map (cone.π f g _))
    (EE.app _).hom _ _ _
    ((homotopy_category.homology_functor _ _ 0).obj (T.obj₂⟦(1 : ℤ)⟧))
    ((homology_functor _ _ 1).obj Y)
    ((homotopy_category.homology_functor A (complex_shape.up ℤ) 0).map T.rotate.mor₃)
    ((homology_functor A (complex_shape.up ℤ) 1).map f)
    (-(EE.app _)).hom,
    apply key, any_goals { apply_instance },
    -- now we need to check that many things commute, and that many things are exact.
    -- It's possible the morphisms above would need to be adjusted with a negation.
  { dsimp [triangle.rotate],
    simp only [functor.map_neg, preadditive.comp_neg, preadditive.neg_comp, neg_neg],
    symmetry,
    apply EE.hom.naturality },
  { exact E1.pair },
  { exact (E1.drop 1).pair },
  { exact (E1.drop 2).pair },
  { exact E2.pair },
  { exact (E2.drop 1).pair },
  { exact (E2.drop 2).pair },
  { simp only [category.id_comp, category.comp_id], refl },
  { rw category.id_comp,
    change _ = (homology_functor _ _ _).map _ ≫ _,
    rw ← functor.map_comp,
    congr' 1, ext i, symmetry, apply biprod.inr_snd_assoc },
  { sorry },
end

end homological_complex
