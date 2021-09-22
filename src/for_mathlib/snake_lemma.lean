import category_theory.preadditive
import category_theory.abelian.projective
import data.matrix.notation
import tactic.interval_cases
import category_theory.abelian.pseudoelements

import for_mathlib.abelian_category
import for_mathlib.fin_functor

noncomputable theory

open category_theory
open category_theory.limits

universe variables v u

namespace eq

variables {X : Type*} {x y : X} (h : x = y)

abbreviation lhs (h : x = y) := x
abbreviation rhs (h : x = y) := y

@[simp] lemma lhs_def : h.lhs = x := rfl
@[simp] lemma rhs_def : h.rhs = y := rfl

end eq

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
`[simp only [category_theory.snake_diagram.o_le_o,
      category_theory.snake_diagram.o_fst, category_theory.snake_diagram.o_snd,
      prod.le_def, and_true, true_and, le_refl],
  dec_trivial! ]

def hom (i j : snake_diagram) (hij : i ≤ j . hom_tac) : i ⟶ j := hom_of_le hij

lemma hom_ext {i j : snake_diagram} (f g : i ⟶ j) : f = g := by ext

section
parameters {C : Type u} [category.{v} C]

parameters (F : fin 4 → fin 3 → C)
parameters (f0 : F 0 0 ⟶ F 0 1) (g0 : F 0 1 ⟶ F 0 2)
parameters (f1 : F 1 0 ⟶ F 1 1) (g1 : F 1 1 ⟶ F 1 2)
parameters (f2 : F 2 0 ⟶ F 2 1) (g2 : F 2 1 ⟶ F 2 2)
parameters (f3 : F 3 0 ⟶ F 3 1) (g3 : F 3 1 ⟶ F 3 2)
parameters (a0 : F 0 0 ⟶ F 1 0) (a1 : F 1 0 ⟶ F 2 0) (a2 : F 2 0 ⟶ F 3 0)
parameters (b0 : F 0 1 ⟶ F 1 1) (b1 : F 1 1 ⟶ F 2 1) (b2 : F 2 1 ⟶ F 3 1)
parameters (c0 : F 0 2 ⟶ F 1 2) (c1 : F 1 2 ⟶ F 2 2) (c2 : F 2 2 ⟶ F 3 2)
parameters (sq00 : a0 ≫ f1 = f0 ≫ b0) (sq01 : b0 ≫ g1 = g0 ≫ c0)
parameters (sq10 : a1 ≫ f2 = f1 ≫ b1) (sq11 : b1 ≫ g2 = g1 ≫ c1)
parameters (sq20 : a2 ≫ f3 = f2 ≫ b2) (sq21 : b2 ≫ g3 = g2 ≫ c2)

namespace mk_functor

def col : Π (j : fin 3), fin 4 ⥤ C
| ⟨0,h⟩ := fin4_functor_mk (flip F 0) a0 a1 a2
| ⟨1,h⟩ := fin4_functor_mk (flip F 1) b0 b1 b2
| ⟨2,h⟩ := fin4_functor_mk (flip F 2) c0 c1 c2
| ⟨j+3,h⟩ := by { exfalso, revert h, dec_trivial }

def row : Π (i : fin 4), fin 3 ⥤ C
| ⟨0,h⟩ := fin3_functor_mk (F 0) f0 g0
| ⟨1,h⟩ := fin3_functor_mk (F 1) f1 g1
| ⟨2,h⟩ := fin3_functor_mk (F 2) f2 g2
| ⟨3,h⟩ := fin3_functor_mk (F 3) f3 g3
| ⟨j+4,h⟩ := by { exfalso, revert h, dec_trivial }

lemma col_obj (i : fin 4) (j : fin 3) : (col j).obj i = F i j :=
by fin_cases i; fin_cases j; refl.

lemma row_obj (i : fin 4) (j : fin 3) : (row i).obj j = F i j :=
by fin_cases i; fin_cases j; refl.

lemma row_eq_col_obj (i : fin 4) (j : fin 3) : (row i).obj j = (col j).obj i :=
(row_obj i j).trans (col_obj i j).symm

def map'  (x y : snake_diagram) (h : x ≤ y) : F x.1 x.2 ⟶ F y.1 y.2 :=
eq_to_hom (by rw [row_obj]) ≫
(row x.1).map h.2.hom ≫ eq_to_hom (by rw [row_obj, col_obj]) ≫
(col y.2).map h.1.hom ≫ eq_to_hom (by rw [col_obj])

lemma map'_id (x : snake_diagram) : map' x x le_rfl = 𝟙 _ :=
by simp only [map', hom_of_le_refl, functor.map_id,
  eq_to_hom_trans, category.id_comp, eq_to_hom_refl]

def square_commutes (i j : fin 4) (k l : fin 3) (hij : i ≤ j) (hkl : k ≤ l) : Prop :=
(col k).map hij.hom ≫ eq_to_hom (by rw [row_obj, col_obj]) ≫
(row j).map hkl.hom =
eq_to_hom (by rw [col_obj]; refl) ≫
map' (o i k) (o j l) ⟨hij, hkl⟩ ≫ eq_to_hom (by rw [row_obj]; refl)

include sq00 sq01 sq10 sq11 sq20 sq21

lemma square_commutes_row (i : fin 4) (k l : fin 3) (hkl : k ≤ l) :
  square_commutes i i k l le_rfl hkl :=
begin
  dsimp [square_commutes, map'],
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc],
  erw [hom_of_le_refl],
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc],
  rw [← category.assoc, eq_comm],
  convert category.comp_id _,
end

lemma square_commutes_col (i j : fin 4) (k : fin 3) (hij : i ≤ j) :
  square_commutes i j k k hij le_rfl :=
begin
  dsimp [square_commutes, map'],
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc],
  erw [hom_of_le_refl],
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc],
  rw [eq_comm],
  convert category.id_comp _,
end

lemma square_commutes_one (i : fin 4) (j : fin 3) (hi : i < 3) (hj : j < 2) :
  square_commutes i (i+1) j (j+1) (by dec_trivial!) (by dec_trivial!) :=
begin
  fin_cases i, swap 4, { exfalso, revert hi, dec_trivial },
  all_goals { fin_cases j, swap 3, { exfalso, revert hj, dec_trivial },
    all_goals {
      simp only [square_commutes, map', eq_to_hom_refl, category.comp_id, category.id_comp],
      assumption }, },
end
.

lemma square_commutes_comp_row (i j k : fin 4) (l m : fin 3)
  (hij : i ≤ j) (hjk : j ≤ k) (hlm : l ≤ m)
  (h1 : square_commutes i j l m hij hlm) (h2 : square_commutes j k l m hjk hlm) :
  square_commutes i k l m (hij.trans hjk) hlm :=
begin
  dsimp [square_commutes, map'] at h1 h2 ⊢,
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc] at h1 h2 ⊢,
  let φ : _ := _, let ψ : _ := _,
  calc _ = φ ≫ h2.lhs : _
     ... = φ ≫ h2.rhs : by { congr' 1, }
     ... = h1.lhs ≫ ψ : _
     ... = h1.rhs ≫ ψ : by { congr' 1, }
     ... = _ : _,
  swap 5, { exact functor.map _ hij.hom },
  swap 4, { refine (eq_to_hom _ ≫ _ ≫ eq_to_hom _),
    swap 2, { apply row_eq_col_obj; assumption },
    swap 3, { symmetry, apply row_eq_col_obj; assumption },
    exact functor.map _ hjk.hom },
  all_goals { dsimp [φ, ψ, eq.lhs_def, eq.rhs_def] },
  { simp only [← functor.map_comp_assoc], refl },
  { simp only [category.assoc], refl },
  { simp only [eq_to_hom_trans, eq_to_hom_trans_assoc, category.assoc],
    dsimp,
    simp only [hom_of_le_refl, eq_to_hom_trans, eq_to_hom_trans_assoc,
      category.id_comp, category.comp_id, category.assoc, ← functor.map_comp_assoc],
    refl, },
end

lemma square_commutes_comp_col (i j : fin 4) (l m n : fin 3)
  (hij : i ≤ j) (hlm : l ≤ m) (hmn : m ≤ n)
  (h1 : square_commutes i j l m hij hlm) (h2 : square_commutes i j m n hij hmn) :
  square_commutes i j l n hij (hlm.trans hmn) :=
begin
  dsimp [square_commutes, map'] at h1 h2 ⊢,
  simp only [map', hom_of_le_refl, functor.map_id, eq_to_hom_trans, eq_to_hom_trans_assoc,
    category.id_comp, category.comp_id, category.assoc] at h1 h2 ⊢,
  let φ : _ := _, let ψ : _ := _,
  calc _ = h1.lhs ≫ φ : _
     ... = h1.rhs ≫ φ : by { congr' 1, }
     ... = ψ ≫ h2.lhs : _
     ... = ψ ≫ h2.rhs : by { congr' 1, }
     ... = _ : _,
  swap 5, { exact functor.map _ hmn.hom },
  swap 4, { refine (eq_to_hom _ ≫ _ ≫ eq_to_hom _),
    swap 2, { symmetry, apply row_eq_col_obj; assumption },
    swap 3, { apply row_eq_col_obj; assumption },
    exact functor.map _ hlm.hom },
  all_goals { dsimp [φ, ψ, eq.lhs_def, eq.rhs_def] },
  { simp only [category.assoc, ← functor.map_comp], refl },
  { simp only [category.assoc], refl },
  { simp only [eq_to_hom_trans, eq_to_hom_trans_assoc, category.assoc],
    dsimp,
    simp only [hom_of_le_refl, eq_to_hom_trans, eq_to_hom_trans_assoc,
      category.id_comp, category.comp_id, category.assoc, ← functor.map_comp_assoc],
    refl, },
end

lemma col_comp_row (i j : fin 4) (k l : fin 3) (hij : i ≤ j) (hkl : k ≤ l) :
  (col k).map hij.hom ≫ eq_to_hom (by rw [row_obj, col_obj]) ≫
  (row j).map hkl.hom =
  eq_to_hom (by rw [col_obj]; refl) ≫
  map' (o i k) (o j l) ⟨hij, hkl⟩ ≫ eq_to_hom (by rw [row_obj]; refl) :=
begin
  cases i with i hi, cases j with j hj, cases k with k hk, cases l with l hl,
  have hkl' := hkl,
  rw [← fin.coe_fin_le, fin.coe_mk, fin.coe_mk] at hij hkl,
  obtain ⟨j, rfl⟩ := nat.exists_eq_add_of_le hij,
  obtain ⟨l, rfl⟩ := nat.exists_eq_add_of_le hkl,
  clear hij,
  induction j with j IHj,
  { apply square_commutes_row; assumption },
  refine square_commutes_comp_row F f0 g0 f1 g1 f2 g2 f3 g3 a0 a1 a2 b0 b1 b2 c0 c1 c2
    sq00 sq01 sq10 sq11 sq20 sq21 ⟨i, hi⟩ ⟨i+j, _⟩ _ _ _ _ _ hkl' _ _,
  { refine lt_trans _ hj, exact lt_add_one (i+j) },
  { simp only [← fin.coe_fin_le, fin.coe_mk], exact le_self_add },
  { simp only [← fin.coe_fin_le, fin.coe_mk], exact (lt_add_one (i+j)).le },
  { refine IHj _ _, },
  clear IHj hkl,
  induction l with l IHl,
  { apply square_commutes_col; assumption },
  refine square_commutes_comp_col F f0 g0 f1 g1 f2 g2 f3 g3 a0 a1 a2 b0 b1 b2 c0 c1 c2
    sq00 sq01 sq10 sq11 sq20 sq21 _ _ ⟨k, hk⟩ ⟨k+l, _⟩ _ _ _ _ _ _,
  { refine lt_trans _ hl, exact lt_add_one (k+l) },
  { simp only [← fin.coe_fin_le, fin.coe_mk], exact le_self_add },
  { simp only [← fin.coe_fin_le, fin.coe_mk], exact (lt_add_one (k+l)).le },
  { refine IHl _ _ _, simp only [← fin.coe_fin_le, fin.coe_mk], exact le_self_add },
  clear IHl,
  convert square_commutes_one F f0 g0 f1 g1 f2 g2 f3 g3 a0 a1 a2 b0 b1 b2 c0 c1 c2
    sq00 sq01 sq10 sq11 sq20 sq21 _ _ _ _ using 2,
  { rw [nat.one_mod, add_assoc, nat.mod_eq_of_lt hj] },
  { rw [nat.one_mod, add_assoc, nat.mod_eq_of_lt hl] },
  { rw [← fin.coe_fin_lt, fin.coe_mk], refine nat.lt_of_succ_lt_succ hj, },
  { rw [← fin.coe_fin_lt, fin.coe_mk], refine nat.lt_of_succ_lt_succ hl, },
end

lemma map'_comp (x y z : snake_diagram) (hxy : x ≤ y) (hyz : y ≤ z) :
  map' x y hxy ≫ map' y z hyz = map' x z (hxy.trans hyz) :=
begin
  delta map',
  slice_lhs 4 7 { rw [eq_to_hom_trans_assoc] },
  rw [col_comp_row],
  { dsimp [map'],
    simp only [map', eq_to_hom_trans_assoc, category.assoc, eq_to_hom_refl,
      category.comp_id, category.id_comp, ← functor.map_comp_assoc],
    refl },
  all_goals { assumption },
end

end mk_functor

include sq00 sq01 sq10 sq11 sq20 sq21

def mk_functor : snake_diagram ⥤ C :=
{ obj := function.uncurry F,
  map := λ x y h, mk_functor.map' F f0 g0 f1 g1 f2 g2 f3 g3 a0 a1 a2 b0 b1 b2 c0 c1 c2 x y h.le,
  map_id' := λ x, mk_functor.map'_id F f0 g0 f1 g1 f2 g2 f3 g3 a0 a1 a2 b0 b1 b2 c0 c1 c2 x,
  map_comp' := λ x y z hxy hyz, by { rw mk_functor.map'_comp; assumption } }

end

section

variables {𝒜 ℬ : Type*} [category 𝒜] [category ℬ]
variables (A : fin 3 → 𝒜) (F : fin 4 → 𝒜 ⥤ ℬ)
variables (f : A 0 ⟶ A 1) (g : A 1 ⟶ A 2) (α : F 0 ⟶ F 1) (β : F 1 ⟶ F 2) (γ : F 2 ⟶ F 3)

def mk_functor' : snake_diagram ⥤ ℬ :=
mk_functor (λ i, (F i).obj ∘ A)
((F 0).map f) ((F 0).map g)
((F 1).map f) ((F 1).map g)
((F 2).map f) ((F 2).map g)
((F 3).map f) ((F 3).map g)
(α.app _) (β.app _) (γ.app _)
(α.app _) (β.app _) (γ.app _)
(α.app _) (β.app _) (γ.app _)
(α.naturality _).symm (α.naturality _).symm
(β.naturality _).symm (β.naturality _).symm
(γ.naturality _).symm (γ.naturality _).symm

end

section

variables {𝒜 ℬ 𝒞 : Type*} [category 𝒜] [category ℬ] [category 𝒞]
variables (A : fin 3 → 𝒜 ⥤ ℬ) (F : fin 4 → ℬ ⥤ 𝒞)
variables (f : A 0 ⟶ A 1) (g : A 1 ⟶ A 2) (α : F 0 ⟶ F 1) (β : F 1 ⟶ F 2) (γ : F 2 ⟶ F 3)

def mk_functor'' : 𝒜 ⥤ snake_diagram ⥤ 𝒞 :=
{ obj := λ x, mk_functor' ![(A 0).obj x, (A 1).obj x, (A 2).obj x] F (f.app x) (g.app x) α β γ,
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry }

end

end snake_diagram

open snake_diagram (o hom)

example (i : fin 4) : o i 0 ⟶ o i 1 := hom (i,0) (i,1)

local notation x `⟶[`D`]` y := D.map (hom x y)

section definitions

variables (𝒜 : Type u) [category.{v} 𝒜] [has_images 𝒜] [has_zero_morphisms 𝒜] [has_kernels 𝒜]

variables {𝒜}

structure is_snake_input (D : snake_diagram ⥤ 𝒜) : Prop :=
(row_exact₁ : exact ((1,0) ⟶[D] (1,1)) ((1,1) ⟶[D] (1,2)))
(row_exact₂ : exact ((2,0) ⟶[D] (2,1)) ((2,1) ⟶[D] (2,2)))
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

end is_snake_input

end definitions

section abelian

open abelian.pseudoelement

variables {𝒜 : Type u} [category.{v} 𝒜] [abelian 𝒜] {D : snake_diagram ⥤ 𝒜}

namespace is_snake_input

lemma row_exact₀ (hD : is_snake_input D) : exact ((0,0) ⟶[D] (0,1)) ((0,1) ⟶[D] (0,2)) :=
begin
  letI := hD.col_mono 2,
  refine exact_of_pseudo_exact _ _ ⟨λ a, zero_of_map_zero _
    (pseudo_injective_of_mono ((0,2) ⟶[D] (1,2))) _ _, λ b, _⟩,
  { rw [← abelian.pseudoelement.comp_apply, ← abelian.pseudoelement.comp_apply,
      ← functor.map_comp, ← functor.map_comp, hD.map_eq (hom _ (0, 1) _ ≫ hom _ (0, 2) _
      ≫ hom (0, 2) (1, 2) _) ((hom (0, 0) (1, 0)) ≫ ((hom _ (1, 1)) ≫ (hom _ (1, 2)))),
      functor.map_comp, functor.map_comp, ((abelian.exact_iff _ _).1 hD.row_exact₁).1, comp_zero,
      zero_apply] },
  { sorry }
end

lemma row_exact₃ (hD : is_snake_input D) : exact ((3,0) ⟶[D] (3,1)) ((3,1) ⟶[D] (3,2)) :=
sorry

lemma row_exact (hD : is_snake_input D) (i : fin 4) :
  exact ((i,0) ⟶[D] (i,1)) ((i,1) ⟶[D] (i,2)) :=
by { fin_cases i, exacts [hD.row_exact₀, hD.row_exact₁, hD.row_exact₂, hD.row_exact₃] }

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

end abelian

end category_theory
