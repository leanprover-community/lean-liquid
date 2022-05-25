import for_mathlib.snake_lemma3
import for_mathlib.les_homology
import for_mathlib.snake_lemma_naturality

noncomputable theory

open category_theory category_theory.limits

variables {C 𝓐 : Type*} [category C] [category 𝓐] [abelian 𝓐]

namespace homological_complex

variables {ι : Type*} {c : complex_shape ι}

local notation x `⟶[`D`]` y := D.map (snake_diagram.hom x y)

-- TODO: Make a general construction, similar to `snake_diagram.mk_functor`
def mk_snake_diagram_nat_trans
  {X Y Z : C ⥤ homological_complex 𝓐 c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (H : ∀ c i, short_exact ((f.app c).f i) ((g.app c).f i))
  {c₁ c₂ : C} (φ : c₁ ⟶ c₂) (i j : ι) (hij : c.rel i j) :
  (snake (f.app c₁) (g.app c₁) (H _) i j hij).snake_diagram ⟶
  (snake (f.app c₂) (g.app c₂) (H _) i j hij).snake_diagram :=
{ app := λ e,
  match e with
  | ⟨⟨0,_⟩,⟨0,_⟩⟩ := (homology_functor _ _ i).map (X.map φ)
  | ⟨⟨0,_⟩,⟨1,_⟩⟩ := (homology_functor _ _ i).map (Y.map φ)
  | ⟨⟨0,_⟩,⟨2,_⟩⟩ := (homology_functor _ _ i).map (Z.map φ)
  | ⟨⟨1,_⟩,⟨0,_⟩⟩ := (mod_boundaries_functor _).map (X.map φ)
  | ⟨⟨1,_⟩,⟨1,_⟩⟩ := (mod_boundaries_functor _).map (Y.map φ)
  | ⟨⟨1,_⟩,⟨2,_⟩⟩ := (mod_boundaries_functor _).map (Z.map φ)
  | ⟨⟨2,_⟩,⟨0,_⟩⟩ := (cycles_functor _ _ _).map (X.map φ)
  | ⟨⟨2,_⟩,⟨1,_⟩⟩ := (cycles_functor _ _ _).map (Y.map φ)
  | ⟨⟨2,_⟩,⟨2,_⟩⟩ := (cycles_functor _ _ _).map (Z.map φ)
  | ⟨⟨3,_⟩,⟨0,_⟩⟩ := (homology_functor _ _ j).map (X.map φ)
  | ⟨⟨3,_⟩,⟨1,_⟩⟩ := (homology_functor _ _ j).map (Y.map φ)
  | ⟨⟨3,_⟩,⟨2,_⟩⟩ := (homology_functor _ _ j).map (Z.map φ)
  | _ := 0 -- impossible case
  end,
  naturality' := begin
    sorry
  end }

lemma δ_natural {X Y Z : C ⥤ homological_complex 𝓐 c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (H : ∀ c i, short_exact ((f.app c).f i) ((g.app c).f i))
  {c₁ c₂ : C} (φ : c₁ ⟶ c₂) (i j : ι) (hij : c.rel i j) :
  δ (f.app c₁) (g.app c₁) (H _) i j hij ≫ (homology_functor _ _ j).map (X.map φ) =
    (homology_functor _ _ i).map (Z.map φ) ≫ δ (f.app c₂) (g.app c₂) (H _) i j hij :=
begin
  let η := mk_snake_diagram_nat_trans f g H φ i j hij,
  apply (snake_lemma.δ_natural η _ _).symm,

  /-
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
  -/
end

end homological_complex
