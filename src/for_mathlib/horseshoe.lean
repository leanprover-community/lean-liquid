import category_theory.derived
import data.matrix.notation

import for_mathlib.snake_lemma
import for_mathlib.delta_functor

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace short_exact_sequence

variables {C : Type u} [category.{v} C] [abelian C] [enough_projectives C]

def horseshoe_step (A : short_exact_sequence C) : short_exact_sequence C :=
{ fst := projective.over A.1,
  snd := (projective.over A.1) ⊞ (projective.over A.3),
  trd := projective.over A.3,
  f := biprod.inl,
  g := biprod.snd,
  mono := infer_instance,
  epi := infer_instance,
  exact := sorry }

end short_exact_sequence
