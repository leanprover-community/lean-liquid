import condensed.proetale_site_as_small

/-!
# Condensed sets

Defines the category of condensed sets and condensed structures.
*Strictly speaking* these are pyknotic, but we hope that in the context of Lean's type theory they
serve the same purpose.
-/

open category_theory category_theory.limits

universes v u

variables {C : Type (u+1)} [category.{v} C]

/-- The category of condensed sets. -/
@[derive category]
def CondensedSet : Type (u+2) := SheafOfTypes.{u+1} proetale_topology.{u}

/-- The category of condensed `A`. Applying this to `A = Type*` is *equivalent* but not the same
as `CondensedSet`. -/
@[derive category]
def Condensed (A : Type (u+2)) [large_category A] : Type (u+2) := Sheaf.{u+1} proetale_topology A

example : category.{u+1} (Condensed Ab.{u+1}) := infer_instance
example : category.{u+1} (Condensed Ring.{u+1}) := infer_instance

open opposite

noncomputable theory

variables (X : (as_small.{u+1} Profinite.{u})ᵒᵖ ⥤ Type (u+1))

lemma maps_comm {S S' : as_small.{u+1} Profinite.{u}} (f : S' ⟶ S) :
  X.map f.op ≫ X.map (pullback.fst : pullback f f ⟶ S').op = X.map f.op ≫ X.map pullback.snd.op :=
by rw [←X.map_comp, ←op_comp, pullback.condition, op_comp, X.map_comp]

def natural_fork {S S' : as_small.{u+1} Profinite.{u}} (f : S' ⟶ S) :
  fork (X.map pullback.fst.op) (X.map pullback.snd.op) :=
fork.of_ι (X.map (quiver.hom.op f)) (maps_comm X f)

-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_terminal
  (X : (as_small.{u+1} Profinite.{u})ᵒᵖ ⥤ Type (u+1)) : Prop := sorry

-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_binary_products
  (X : (as_small.{u+1} Profinite.{u})ᵒᵖ ⥤ Type (u+1)) : Prop := sorry

structure condensed_type_condition : Prop :=
(empty : nonempty X.preserves_terminal)
(bin_prod : nonempty X.preserves_binary_products)
(pullbacks : ∀ {S S' : as_small.{u+1} Profinite.{u}} (f : S' ⟶ S) [epi f],
  nonempty (is_limit (natural_fork X f)))

-- (BM): I'm 90% sure this is true as stated, the forward direction is about halfway done.
lemma sheaf_condition_iff :
  presieve.is_sheaf proetale_topology X ↔ condensed_type_condition X :=
sorry

-- TODO: Double check this definition...
def embed_Top : Top.{u} ⥤ CondensedSet.{u} :=
{ obj := λ T, ⟨as_small.down.op ⋙ Profinite.to_Top.op ⋙ yoneda.obj T ⋙ ulift_functor.{u+1}, sorry⟩,
  map := λ T₁ T₂ f, whisker_left _ $ whisker_left _ $ whisker_right (yoneda.map f) _ }

/-
-- TODO: State `sheaf_condition_iff` for presheaves taking values in `A` for `A` with appropriate
-- structure.
-- TODO: Use `sheaf_condition_iff` to define the functor of Example 1.5, it might look like this:
def embed_Top : Top.{u} ⥤ CondensedSet.{u} :=
{ obj := λ T, ⟨Profinite.to_Top.op ⋙ yoneda.obj T,
  begin
    rw sheaf_condition_iff, refine ⟨⟨_⟩, ⟨_⟩, _⟩,
    all_goals { sorry }
  end⟩,
  map := λ T₁ T₂ f, whisker_left Profinite.to_Top.op (yoneda.map f) }
-/

-- TODO: Use the above to prove the first part of Proposition 1.7:
lemma embed_Top_faithful : faithful embed_Top := sorry

-- TODO: Construct the left adjoint to `embed_Top` as in the second part of Proposition 1.7.
