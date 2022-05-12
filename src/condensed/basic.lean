import category_theory.sites.limits
import algebra.category.Group.filtered_colimits
import algebra.category.Group.abelian
import topology.category.Profinite.projective

import for_mathlib.presieve
import for_mathlib.Profinite.disjoint_union
import for_mathlib.abelian_sheaves.main
import for_mathlib.AddCommGroup.explicit_limits

import condensed.proetale_site
import condensed.is_proetale_sheaf


/-!
# Condensed sets

Defines the category of condensed sets and condensed structures.
*Strictly speaking* these are pyknotic, but we hope that in the context of Lean's type theory they
serve the same purpose.

-/

open category_theory category_theory.limits

universes w v u

variables {C : Type u} [category.{v} C]

/-- The category of condensed sets. -/
@[derive category]
def CondensedSet : Type (u+2) := Sheaf proetale_topology.{u} (Type (u+1))

/-- The category of condensed `A`. Applying this to `A = Type*` is *equivalent* but not the same
as `CondensedSet`. -/
@[derive category]
def Condensed (C : Type u) [category.{v} C] := Sheaf proetale_topology.{w} C

example : category.{u+1} (Condensed.{u} Ab.{u+1}) := infer_instance
example : category.{u+37} (Condensed.{u} Ring.{u+37}) := infer_instance

open opposite

noncomputable theory

variables (X : Profinite.{u}ᵒᵖ ⥤ Type (u+1))
variables (P : Profinite.{w}ᵒᵖ ⥤ Type u)

lemma maps_comm {S S' : Profinite.{u}} (f : S' ⟶ S) :
  X.map f.op ≫ X.map (pullback.fst : pullback f f ⟶ S').op = X.map f.op ≫ X.map pullback.snd.op :=
by rw [←X.map_comp, ←op_comp, pullback.condition, op_comp, X.map_comp]

def natural_fork {S S' : Profinite.{u}} (f : S' ⟶ S) :
  fork (X.map pullback.fst.op) (X.map pullback.snd.op) :=
fork.of_ι (X.map (quiver.hom.op f)) (maps_comm X f)

section

/-
There are several files where the instances below are needed, but are not found automatically
because the universe parameters involve things like `max v w` where `v = u+1` and `w = u`.
So we just add them manually here.
-/

instance : has_limits CondensedSet.{u} :=
Sheaf.category_theory.limits.has_limits.{(u+2) u (u+1)}

instance : has_colimits CondensedSet.{u} :=
Sheaf.category_theory.limits.has_colimits.{(u+2) u (u+1)}

instance (C : Type (u+2)) [category.{u+1} C] [has_limits C] :
  has_limits (Condensed.{u} C) :=
Sheaf.category_theory.limits.has_limits.{(u+2) u (u+1)}

instance (C : Type (u+2)) [category.{u+1} C]
  [concrete_category.{u+1} C]
  [reflects_isomorphisms (forget C)]
  [preserves_limits (forget C)]
  [has_colimits C]
  [∀ (X : Profinite.{u}),
    preserves_colimits_of_shape (proetale_topology.cover X)ᵒᵖ (forget C)]
  [∀ (P : Profiniteᵒᵖ ⥤ C) (X : Profinite)
    (S : proetale_topology.cover X), has_multiequalizer (S.index P)] :
  has_colimits (Condensed.{u} C) :=
Sheaf.category_theory.limits.has_colimits.{(u+2) u (u+1)}

instance (X : Profinite) : is_filtered  (proetale_topology.cover X)ᵒᵖ :=
 by apply_instance

set_option pp.universes true

instance Condensed_Ab_has_colimits : has_colimits (Condensed.{u} Ab.{u+1}) :=
Sheaf.category_theory.limits.has_colimits.{(u+2) u (u+1)}

instance Condensed_Ab_has_limits : has_limits (Condensed.{u} Ab.{u+1}) :=
Sheaf.category_theory.limits.has_limits.{(u+2) u (u+1)}

instance : abelian (Condensed Ab.{u+1}) :=
@category_theory.Sheaf.abelian.{(u+2) u (u+1)} Profinite.{u} _
  proetale_topology Ab.{u+1} _ _ _ _ _ _ _ _

end

/-
-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_terminal
  (X : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := by admit

-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_binary_products
  (X : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := by admit

structure condensed_type_condition : Prop :=
(empty : nonempty X.preserves_terminal)
(bin_prod : nonempty X.preserves_binary_products)
(pullbacks : ∀ {S S' : Profinite.{u}} (f : S' ⟶ S) [epi f],
  nonempty (is_limit (natural_fork X f)))

-- (BM): I'm 90% sure this is true as stated, the forward direction is about halfway done.
lemma sheaf_condition_iff :
  presieve.is_sheaf proetale_topology X ↔ condensed_type_condition X :=
by admit
-/

-- See `Top_to_Condensed` in `condensed/top_comparison.lean`.
/-
-- TODO: Double check this definition...
def embed_Top : Top.{u} ⥤ CondensedSet.{u} :=
{ obj := λ T, ⟨Profinite.to_Top.op ⋙ yoneda.obj T ⋙ ulift_functor.{u+1}, by admit⟩,
  map := λ T₁ T₂ f, ⟨whisker_left _ $ whisker_right (yoneda.map f) _⟩ }
-/

/-
-- TODO: State `sheaf_condition_iff` for presheaves taking values in `A` for `A` with appropriate
-- structure.
-- TODO: Use `sheaf_condition_iff` to define the functor of Example 1.5, it might look like this:
def embed_Top : Top.{u} ⥤ CondensedSet.{u} :=
{ obj := λ T, ⟨Profinite.to_Top.op ⋙ yoneda.obj T,
  begin
    rw sheaf_condition_iff, refine ⟨⟨_⟩, ⟨_⟩, _⟩,
    all_goals { admit }
  end⟩,
  map := λ T₁ T₂ f, whisker_left Profinite.to_Top.op (yoneda.map f) }
-/

-- TODO: Use the above to prove the first part of Proposition 1.7:
-- lemma embed_Top_faithful : faithful embed_Top := by admit

-- TODO: Construct the left adjoint to `embed_Top` as in the second part of Proposition 1.7.
