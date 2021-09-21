import category_theory.preadditive
import category_theory.abelian.projective
import tactic.interval_cases

import for_mathlib.abelian_category

noncomputable theory

open category_theory
open category_theory.limits

universe variables v u

lemma prod.le_def {X Y : Type*} [has_le X] [has_le Y] (a b : X × Y) :
  a ≤ b ↔ a.1 ≤ b.1 ∧ a.2 ≤ b.2 := iff.rfl

namespace category_theory

/-- The base diagram for the snake lemma. The object are indexed by `fin 4 × fin 3`:

(0,0) --> (0,1) --> (0,2)              | the kernels
  |         |         |
  v         v         v
(1,0) --> (1,1) --> (1,2)              | the first exact row
  |         |         |
  v         v         v
(2,0) --> (2,1) --> (2,2)              | the second exact row
  |         |         |
  v         v         v
(3,0) --> (3,1) --> (3,2)              | the cokernels

-/
@[derive [preorder, decidable_eq]]
def snake_diagram := fin 4 × fin 3

namespace snake_diagram

@[simps]
def o (i : fin 4) (j : fin 3) : snake_diagram := (i,j)

@[simp] lemma o_le_o (i j : fin 4) (k l : fin 3) :
  o i k ≤ o j l ↔ i ≤ j ∧ k ≤ l := iff.rfl

meta def hom_tac : tactic unit :=
`[ simp only [category_theory.snake_diagram.o_le_o,
       category_theory.snake_diagram.o_fst, category_theory.snake_diagram.o_snd,
      prod.le_def, and_true, true_and, le_refl],
   dec_trivial! ]

def hom (i j : snake_diagram) (hij : i ≤ j . hom_tac) : i ⟶ j := hom_of_le hij

lemma hom_ext {i j : snake_diagram} (f g : i ⟶ j) : f = g := by ext

section
variables {C : Type u} [category.{v} C]

variables (F : fin 4 → fin 3 → C)
variables (f0 : F 0 0 ⟶ F 0 1) (g0 : F 0 1 ⟶ F 0 2)
variables (f1 : F 1 0 ⟶ F 1 1) (g1 : F 1 1 ⟶ F 1 2)
variables (f2 : F 2 0 ⟶ F 2 1) (g2 : F 2 1 ⟶ F 2 2)
variables (f3 : F 3 0 ⟶ F 3 1) (g3 : F 3 1 ⟶ F 3 2)
variables (a0 : F 0 0 ⟶ F 1 0) (a1 : F 1 0 ⟶ F 2 0) (a2 : F 2 0 ⟶ F 3 0)
variables (b0 : F 0 1 ⟶ F 1 1) (b1 : F 1 1 ⟶ F 2 1) (b2 : F 2 1 ⟶ F 3 1)
variables (c0 : F 0 2 ⟶ F 1 2) (c1 : F 1 2 ⟶ F 2 2) (c2 : F 2 2 ⟶ F 3 2)
variables (sq00 : a0 ≫ f1 = f0 ≫ b0) (sq01 : b0 ≫ g1 = g0 ≫ c0)
-- variables (sq00 : a0 ≫ f1 = f0 ≫ b0) (sq01 : b0 ≫ g1 = g0 ≫ c0)
-- variables (sq00 : a0 ≫ f1 = f0 ≫ b0) (sq01 : b0 ≫ g1 = g0 ≫ c0)

def mk_functor : snake_diagram ⥤ C :=
{ obj := function.uncurry F,
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry }

end

end snake_diagram

open snake_diagram (o hom)

example (i : fin 4) : o i 0 ⟶ o i 1 := hom (i,0) (i,1)

local notation x `⟶[`D`]` y := D.map (hom x y)

variables (𝒜 : Type u) [category.{v} 𝒜] [has_images 𝒜] [has_zero_morphisms 𝒜] [has_kernels 𝒜]

variables {𝒜}

structure is_snake_input (D : snake_diagram ⥤ 𝒜) : Prop :=
(row_exact : ∀ i, exact ((i,0) ⟶[D] (i,1)) ((i,1) ⟶[D] (i,2)))
(col_exact₁ : ∀ j, exact ((0,j) ⟶[D] (1,j)) ((1,j) ⟶[D] (2,j)))
(col_exact₂ : ∀ j, exact ((1,j) ⟶[D] (2,j)) ((2,j) ⟶[D] (3,j)))
(col_mono : ∀ j, mono ((0,j) ⟶[D] (1,j)))
(col_epi  : ∀ j, mono ((2,j) ⟶[D] (3,j)))
(row_mono : mono ((2,0) ⟶[D] (2,1)))
(row_epi  : epi ((1,1) ⟶[D] (1,2)))

namespace is_snake_input

variables {D : snake_diagram ⥤ 𝒜}

@[nolint unused_arguments]
lemma map_eq (hD : is_snake_input D) {x y : snake_diagram} (f g : x ⟶ y) : D.map f = D.map g :=
congr_arg _ (snake_diagram.hom_ext _ _)

@[nolint unused_arguments]
lemma map_eq_id (hD : is_snake_input D) {x : snake_diagram} (f : x ⟶ x) : D.map f = 𝟙 _ :=
by rw [snake_diagram.hom_ext f (𝟙 x), D.map_id]

lemma hom_eq_zero₁ (hD : is_snake_input D) {x y : snake_diagram} (f : x ⟶ y)
  (h : x.1 < 2 ∧ x.1 + 1 < y.1 . snake_diagram.hom_tac) : D.map f = 0 :=
begin
  cases x with i j, cases y with k l, cases h with h₀ h₁, rcases f with ⟨⟨⟨hik, hjl⟩⟩⟩,
  dsimp at h₀ h₁ hik hjl,
  let f₁ := hom (i,j) (i+1,j),
  let f₂ := hom (i+1,j) (i+2,j),
  let f₃ := hom (i+2,j) (k,l),
  calc D.map _
      = D.map ((f₁ ≫ f₂) ≫ f₃)             : hD.map_eq _ _
  ... = ((D.map f₁) ≫ D.map f₂) ≫ D.map f₃ : by simp only [D.map_comp]
  ... = 0 ≫ D.map f₃                        : _
  ... = 0                                   : zero_comp,
  congr' 1,
  obtain (rfl|rfl) : i = 0 ∨ i = 1, { dec_trivial! },
  { exact (hD.col_exact₁ j).w },
  { exact (hD.col_exact₂ j).w },
end

lemma hom_eq_zero₂ (hD : is_snake_input D) {x y : snake_diagram} (f : x ⟶ y)
  (h : x.2 = 0 ∧ y.2 = 2 . snake_diagram.hom_tac) : D.map f = 0 :=
begin
  cases x with i j, cases y with k l, rcases f with ⟨⟨⟨hik, hjl⟩⟩⟩,
  dsimp at h hik hjl, rcases h with ⟨rfl, rfl⟩,
  let f₁ := hom (i,0) (i,1),
  let f₂ := hom (i,1) (i,2),
  let f₃ := hom (i,2) (k,2),
  calc D.map _
      = D.map ((f₁ ≫ f₂) ≫ f₃)             : hD.map_eq _ _
  ... = ((D.map f₁) ≫ D.map f₂) ≫ D.map f₃ : by simp only [D.map_comp]
  ... = 0                                    : by rw [(hD.row_exact i).w, zero_comp]
end

example (hD : is_snake_input D) (f : (o 1 0) ⟶ (o 2 2)) : D.map f = 0 := hD.hom_eq_zero₂ f

end is_snake_input

variables (𝒜)

structure snake_input extends snake_diagram ⥤ 𝒜 :=
(is_snake_input : is_snake_input to_functor)

namespace snake_input

instance : category (snake_input 𝒜) := induced_category.category to_functor

@[simps] def proj (x : snake_diagram) : snake_input 𝒜 ⥤ 𝒜 :=
induced_functor _ ⋙ (evaluation _ _).obj x

end snake_input

class has_snake_lemma :=
(δ : snake_input.proj 𝒜 (0,2) ⟶ snake_input.proj 𝒜 (3,0))
(exact_δ : ∀ (D : snake_input 𝒜), exact ((0,1) ⟶[D] (0,2)) (δ.app D))
(δ_exact : ∀ (D : snake_input 𝒜), exact (δ.app D) ((3,0) ⟶[D.1] (3,1))) -- why can't I write `⟶[D]`

namespace snake_lemma

variables [has_snake_lemma 𝒜]

variables {𝒜}

def δ (D : snake_input 𝒜) : D.obj (0,2) ⟶ D.obj (3,0) := has_snake_lemma.δ.app D

lemma exact_δ (D : snake_input 𝒜) : exact ((0,1) ⟶[D] (0,2)) (δ D) :=
has_snake_lemma.exact_δ D

lemma δ_exact (D : snake_input 𝒜) : exact (δ D) ((3,0) ⟶[D] (3,1)) :=
has_snake_lemma.δ_exact D

end snake_lemma

end category_theory
