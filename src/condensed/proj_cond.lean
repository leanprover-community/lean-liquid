/-
-- This stuff is probably not needed anymore.
import category_theory.preadditive.projective
import condensed.condensed

namespace Profinite

open category_theory
open category_theory.limits

-- TODO: generalize
instance : projective (⊥_ Profinite) :=
{ factors := λ E X f e _, ⟨limits.initial.to _, by simp⟩ }

instance : has_initial (as_small Profinite) := sorry

universe v
variables {C : Type*} [category.{v+1} C] (F : (as_small.{v+1} Profinite.{v})ᵒᵖ ⥤ C)

-- I assume we want this to be a prop, but `is_terminal` and `preserves_limits_of_shape`
-- both contain data.
structure extr_sheaf_cond : Prop :=
(is_terminal : nonempty (is_terminal (F.obj (opposite.op (⊥_ _)))))
(preserves : ∀ (X Y : as_small.{v+1} Profinite.{v}) [projective X] [projective Y],
  nonempty (preserves_limit (pair (opposite.op X) (opposite.op Y)) F))

def proetale_topology' : grothendieck_topology (as_small.{v+1} Profinite.{v}) :=
sorry

theorem extr_sheaf_iff : extr_sheaf_cond F ↔ presheaf.is_sheaf proetale_topology' F := sorry

end Profinite
-/
