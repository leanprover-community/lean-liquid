
import category_theory.derived

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace chain_complex

variables {C : Type u} [category.{v} C]
variables [preadditive C] [has_zero_object C] [has_equalizers C] [has_images C]

structure is_projective_resolution (P : chain_complex C ℕ) (Z : C)
  (π : P ⟶ ((chain_complex.single₀ C).obj Z)) : Prop :=
(projective : ∀ n, projective (P.X n) . tactic.apply_instance)
(exact₀ : exact (P.d 1 0) (π.f 0) . tactic.apply_instance)
(exact : ∀ n, exact (P.d (n+2) (n+1)) (P.d (n+1) n) . tactic.apply_instance)
(epi : epi (π.f 0) . tactic.apply_instance)

def is_projective_resolution.mk_ProjectiveResolution (P : chain_complex C ℕ) (Z : C)
  (π : P ⟶ ((chain_complex.single₀ C).obj Z)) (h : P.is_projective_resolution Z π) :
  ProjectiveResolution Z :=
{ complex := P,
  π := π,
  .. h }

end chain_complex
