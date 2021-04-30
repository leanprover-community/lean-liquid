import data.real.basic
import for_mathlib.seminormed_category.basic
import category_theory.preadditive.additive_functor

namespace category_theory

namespace functor

def bounded_by {J C : Type*} [category J] [category C] [semi_normed_category C]
  (F : J ⥤ C) (c : ℝ) : Prop := 0 ≤ c ∧ ∀ {a b : J} (f : a ⟶ b), ∥ F.map f ∥ ≤ c

class bounded {J C : Type*} [category J] [category C] [semi_normed_category C]
  (F : J ⥤ C) : Prop :=
(bounded : ∃ c : ℝ, 0 ≤ c ∧  F.bounded_by c)

noncomputable
def norm {J C : Type*} [category J] [category C] [semi_normed_category C]
  (F : J ⥤ C) [bounded F] : ℝ := Inf { a | 0 ≤ a ∧ F.bounded_by a }

lemma norm_nonneg {J C : Type*} [category J] [category C] [semi_normed_category C]
  (F : J ⥤ C) [bounded F] : 0 ≤ F.norm :=
real.lb_le_Inf _ bounded.bounded (λ c hc, hc.1)

lemma le_norm {J C : Type*} [category J] [category C] [semi_normed_category C]
  (F : J ⥤ C) [bounded F] {a b : J} (f : a ⟶ b) : ∥ F.map f ∥ ≤ F.norm :=
begin
  erw real.le_Inf,
  { intros c hc,
    apply hc.2.2 },
  { exact bounded.bounded },
  { use 0,
    intros c hc,
    exact hc.1 }
end

class norm_compat {C D : Type*} [category C] [category D] [semi_normed_category C]
  [semi_normed_category D] (F : C ⥤ D) : Prop :=
(norm_eq' [] : ∀ {X Y : C} (f : X ⟶ Y), ∥ F.map f ∥ = ∥ f ∥ . obviously)

restate_axiom norm_compat.norm_eq'
attribute [simp] norm_compat.norm_eq

end functor

namespace nat_trans

def bounded_by {J C : Type*} [category J] [category C] [semi_normed_category C]
  {F G : J ⥤ C} (η : nat_trans F G) (c : ℝ) : Prop := 0 ≤ c ∧ ∀ j : J, ∥ η.app j ∥ ≤ c

class bounded {J C : Type*} [category J] [category C] [semi_normed_category C]
  {F G : J ⥤ C} (η : F ⟶ G) : Prop :=
(bounded : ∃ c : ℝ, 0 ≤ c ∧ η.bounded_by c)

noncomputable
def norm {J C : Type*} [category J] [category C] [semi_normed_category C]
  {F G : J ⥤ C} (η : F ⟶ G) [bounded η] : ℝ := Inf { a | 0 ≤ a ∧ η.bounded_by a }

lemma norm_nonneg {J C : Type*} [category J] [category C] [semi_normed_category C]
  {F G : J ⥤ C} (η : F ⟶ G) [bounded η] : 0 ≤ η.norm :=
real.lb_le_Inf _ bounded.bounded $ λ c hc, hc.1

lemma le_norm {J C : Type*} [category J] [category C] [semi_normed_category C]
  {F G : J ⥤ C} (η : F ⟶ G) [bounded η] (j : J) : ∥ η.app j ∥ ≤ η.norm :=
begin
  erw real.le_Inf,
  { intros c hc,
    apply hc.2.2 },
  { exact bounded.bounded },
  { use 0,
    intros c hc,
    exact hc.1 }
end

end nat_trans

end category_theory
