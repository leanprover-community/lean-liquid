import condensed.proetale_site

/-!
# Condensed sets

Defines the category of condensed sets and condensed structures.
*Strictly speaking* these are pyknotic, but we hope that in the context of Lean's type theory they
serve the same purpose.
-/

open category_theory category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

/-- The category of condensed sets. -/
@[derive category]
def CondensedSet : Type (u+1) := SheafOfTypes.{u} proetale_topology.{u}

/-- The category of condensed `A`. Applying this to `A = Type*` is *equivalent* but not the same
as `CondensedSet`. -/
@[derive category]
def Condensed (A : Type (u+1)) [large_category A] : Type (u+1) := Sheaf.{u} proetale_topology A

example : category.{u+1} (Condensed Ab.{u}) := infer_instance
example : category.{u+1} (Condensed Ring.{u}) := infer_instance

open opposite

noncomputable theory

variables (P : Profinite.{u}ᵒᵖ ⥤ Type u)
lemma maps_comm {S S' : Profinite.{u}} (f : S' ⟶ S) :
  P.map f.op ≫ P.map (pullback.fst : pullback f f ⟶ S').op = P.map f.op ≫ P.map pullback.snd.op :=
by rw [←P.map_comp, ←op_comp, pullback.condition, op_comp, P.map_comp]

def natural_fork {S S' : Profinite.{u}} (f : S' ⟶ S) :
  fork (P.map pullback.fst.op) (P.map pullback.snd.op) :=
fork.of_ι (P.map (quiver.hom.op f)) (maps_comm P f)

-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_terminal (P : Profinite.{u}ᵒᵖ ⥤ Type u) : Prop := sorry
-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_binary_products (P : Profinite.{u}ᵒᵖ ⥤ Type u) : Prop := sorry

structure condensed_type_condition : Prop :=
(empty : nonempty P.preserves_terminal)
(bin_prod : nonempty P.preserves_binary_products)
(pullbacks : ∀ {S S' : Profinite.{u}} (f : S' ⟶ S) [epi f], nonempty (is_limit (natural_fork P f)))

-- (BM): I'm 90% sure this is true as stated, the forward direction is about halfway done.
lemma sheaf_condition_iff :
  presieve.is_sheaf proetale_topology P ↔ condensed_type_condition P :=
sorry

-- TODO: State `sheaf_condition_iff` for presheaves taking values in `A` for `A` with appropriate
-- structure.
-- TODO: Use `sheaf_condition_iff` to define the functor of Example 1.5, it might look like this:
def embed_Top : Top.{u} ⥤ CondensedSet.{u} :=
{ obj := λ T, ⟨Profinite_to_Top.op ⋙ yoneda.obj T, sorry⟩,
  map := λ T₁ T₂ f, whisker_left Profinite_to_Top.op (yoneda.map f) }

-- TODO: Use the above to prove the first part of Proposition 1.7:
lemma embed_Top_faithful : faithful embed_Top := sorry

-- TODO: Construct the left adjoint to `embed_Top` as in the second part of Proposition 1.7.
