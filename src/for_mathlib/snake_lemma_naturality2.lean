import for_mathlib.snake_lemma3
import for_mathlib.les_homology

noncomputable theory

open category_theory category_theory.limits

variables {C 𝓐 : Type*} [category C] [category 𝓐] [abelian 𝓐]

namespace homological_complex

variables {ι : Type*} {c : complex_shape ι}

local notation x `⟶[`D`]` y := D.map (snake_diagram.hom x y)

lemma δ_natural {X Y Z : C ⥤ homological_complex 𝓐 c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (H : ∀ c i, short_exact ((f.app c).f i) ((g.app c).f i))
  {c₁ c₂ : C} (φ : c₁ ⟶ c₂) (i j : ι) (hij : c.rel i j) :
  δ (f.app c₁) (g.app c₁) (H _) i j hij ≫ (homology_functor _ _ j).map (X.map φ) =
    (homology_functor _ _ i).map (Z.map φ) ≫ δ (f.app c₂) (g.app c₂) (H _) i j hij :=
begin
  delta δ snake.δ,
  have h1 : snake_diagram.hom (1,0) (2,1) =
    snake_diagram.hom (1,0) (1,1) ≫ snake_diagram.hom (1,1) (2,1) := snake_diagram.hom_ext _ _,
  generalize_proofs _ _ _ _ _ _ S₁ hS₁ S₂ hS₂,
  rw [← cancel_epi hS₁.to_kernel', ← cancel_mono hS₂.cokernel_to'],
  have aux1 : (homology_functor 𝓐 c j).map (X.map φ) ≫ hS₂.cokernel_to' = hS₁.cokernel_to' ≫
      (cokernel.map _ _
        ((mod_boundaries_functor i).map (X.map φ))
        ((cycles_functor _ _ j).map (Y.map φ)) _),
  swap 3,
  { dsimp only [snake.snake_diagram],
    simp only [h1, category_theory.functor.map_comp, category.assoc, ← nat_trans.naturality,
      snake_diagram.mk_functor_map_f1, snake_diagram.mk_functor_map_b1,
      ← mod_boundaries_functor_map],
    simp only [← category_theory.functor.map_comp_assoc, ← nat_trans.naturality], },
  { delta is_snake_input.cokernel_to',
    sorry },
  sorry
  -- simp only [category.assoc],
  -- delta is_snake_input.to_kernel' is_snake_input.cokernel_to',
end

end homological_complex
