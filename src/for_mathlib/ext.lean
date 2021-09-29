import category_theory.abelian.ext

import for_mathlib.derived_functor

noncomputable theory

universe variables uᵣ v u

open category_theory opposite

namespace Ext

variables (R : Type uᵣ) [ring R] {C : Type u} [category.{v} C] [abelian C] [linear R C]
  [enough_projectives C]

local notation `Ext` i `,` A `,` B := ((Ext R C i).obj (op A)).obj B

def δ (n : ℕ) (A : short_exact_sequence C) (B : C) :
  (Ext n , A.1 , B) ⟶ (Ext (n+1) , A.3 , B) :=
let E  := (((linear_yoneda R C).obj B).right_op.left_derived n),
    E' := (((linear_yoneda R C).obj B).right_op.left_derived (n+1)) in
quiver.hom.unop (show E'.obj A.3 ⟶ E.obj A.1, from functor.left_derived.δ _ _ _)

lemma six_term_exact_seq (n : ℕ) (A : short_exact_sequence C) (B : C) :
  exact_seq (Module.{v} R) [
    ((«Ext» R C n).map A.g.op).app B, ((«Ext» R C n).map A.f.op).app B,
    δ R n A B,
    ((«Ext» R C (n+1)).map A.g.op).app B, ((«Ext» R C (n+1)).map A.f.op).app B
    ] := sorry
-- this need `exact_seq.unop`

end «Ext»
