import for_mathlib.snake_lemma2
import for_mathlib.homology
import for_mathlib.exact_seq2

noncomputable theory

open category_theory category_theory.limits

variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]

namespace category_theory

local notation `kernel_map`   := kernel.map _ _ _ _
local notation `cokernel_map` := cokernel.map _ _ _ _

namespace snake

lemma mk_of_homology (X Y Z : cochain_complex 𝒜 ℤ)
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [exact (f.f (-1)) (g.f (-1))]
  [exact (f.f 0) (g.f 0)]
  [exact (f.f 1) (g.f 1)]
  [epi (g.f (-1))]
  [epi (g.f 0)]
  [epi (g.f 1)]
  [mono (f.f (-1))]
  [mono (f.f 0)]
  [mono (f.f 1)] : snake
  (kernel (X.d_to 0))
  (kernel (Y.d_to 0))
  (kernel (Z.d_to 0))
  (X.X_prev 0)
  (Y.X_prev 0)
  (Z.X_prev 0)
  (kernel (X.d_from 0))
  (kernel (Y.d_from 0))
  (kernel (Z.d_from 0))
  ((homology_functor _ _ 0).obj X)
  ((homology_functor _ _ 0).obj Y)
  ((homology_functor _ _ 0).obj Z)
  (kernel.lift _ (kernel.ι _ ≫ (f.prev _)) sorry)
  (kernel.lift _ (kernel.ι _ ≫ (g.prev _)) sorry)
  (kernel.ι _)
  (kernel.ι _)
  (kernel.ι _)
  (f.prev _)
  (g.prev _)
  (kernel.lift _ (X.d_to _) sorry)
  (kernel.lift _ (Y.d_to _) sorry)
  (kernel.lift _ (Z.d_to _) sorry)
  (kernel.lift _ (kernel.ι _ ≫ f.f _) sorry)
  (kernel.lift _ (kernel.ι _ ≫ g.f _) sorry)
  (homology.π' _ _ _)
  (homology.π' _ _ _)
  (homology.π' _ _ _)
  ((homology_functor _ _ _).map f)
  ((homology_functor _ _ _).map g) := sorry

end snake

end category_theory
