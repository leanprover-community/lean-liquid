import challenge -- imports the entire proof of the Liquid Tensor Experiment.

/-!

# Profinite sets

This file explains the structure of profinite sets.

Lean uses type theory, so strictly speaking we are setting up the theory
of profinite types. But for mathematics of this nature, sets and types
are to all intents and purposes the same thing, and it makes no difference
to the underlying mathematics.

-/

open category_theory opposite -- so we can write `grothendieck_topology` instead
-- of `category_theory.grothendieck_topology` and `op` instead of `opposite.op`
open_locale liquid_tensor_experiment -- This introduces a coercion from
-- functors to functions, used once below.

attribute [instance] functor_coe_to_fun
/-
Set-theoretically one can think of `Profinite.{0}` as the collection of profinite sets.
Type-theoretically it's the class of profinite spaces whose underlying type
lives in `Type = Type 0`. The type of `Profinite.{0}` is `Type 1`, which is the type-theoretic
version of the set-theoretic concept of an object being a class (so possibly too big to be a set).
-/
example : Type 1 := Profinite.{0} -- Set-theoretic translation: `Profinite.{0}` is a collection of
                                  -- objects, possibly too big to be a set.
example (X : Profinite.{0}) : Type := X -- Set-theoretic translation: The objects of `Profinite.{0}`
                                        -- can be thought of as sets.
/-
Any profinite set is a compact, Hausdorff, totally disconnected topological space.
It's the job of Lean's type class inference system to prove these facts automatically.
-/
example (X : Profinite.{0}) : topological_space X := infer_instance
example (X : Profinite.{0}) : compact_space X := infer_instance
example (X : Profinite.{0}) : t2_space X := infer_instance
example (X : Profinite.{0}) : totally_disconnected_space X := infer_instance

/-
Conversely, any topological space which is compact, Hausdorff and
totally disconnected can be considered as a profinite set.
-/
example (X : Type)
  [topological_space X]
  [compact_space X]
  [t2_space X]
  [totally_disconnected_space X] :
  Profinite.{0} :=
Profinite.of X -- `Profinite.of` is the function which makes the object in the category from the
               -- topological space. Lean is pedantic about the difference.

/-
`C(X,Y)` is the type of continuous maps from `X` to `Y`. The longer
arrow `X ⟶ Y` denotes the type of morphisms from `X` to `Y` in the category `Profinite.{0}`.
The next example shows that, by definition, the morphisms in the category
are the continuous maps.
-/
example (X Y : Profinite.{0}) : (X ⟶ Y : Type) = C(X,Y) := rfl

/-
The term `proetale_topology` is the name of a Grothendieck topology on `Profinite.{0}`
which is used in condensed mathematics. In the next example we'll see that the definition
of this topology is what you would expect.
-/
example : grothendieck_topology Profinite.{0} := proetale_topology

/-
This example shows that the sheaf condition with respect to this Grothendieck topology,
for a presheaf of abelian groups on `Profinite.{0}`, is equivalent to the usual definition.
-/
example (F : Profinite.{0}ᵒᵖ ⥤ Ab.{1}) : -- Let `F` be a presheaf of ab groups on `Profinite.{0}`
  presheaf.is_sheaf proetale_topology F -- `F` is a sheaf for `proetale_topology` if and only if...
  ↔
  ∀ (α : Fintype.{0}) -- For any finite indexing type `α`,
    (B : Profinite.{0}) -- profinite set `B`,
    (X : α → Profinite.{0}) -- family of profinite sets `X` indexed by `α`
    (π : Π i, X i ⟶ B) -- which map to `B` with a family of maps `π`,
    (hπ : ∀ b : B, ∃ i (x : X i), π i x = b) -- such that `π` is jointly surjective,
    (x : Π i, F (op $ X i)) -- and all families of elements `x i : F (op $ X i)`,
    (hx : ∀ i j : α, -- which are compatible on pullbacks `X i ×_{B} X j`
      F.map (limits.pullback.fst : limits.pullback (π i) (π j) ⟶ X i).op (x i) =
      F.map (limits.pullback.snd : limits.pullback (π i) (π j) ⟶ X j).op (x j)),
    ∃! s : F.obj (op B), -- there is a unique `s : F (op B)`
      ∀ i, F.map (π i).op s = x i  -- which restricts to `x i` over `X i` for all `i`.
    :=
begin
  -- it suffices to check the underlying sheaf of types is a presheaf
  rw presheaf.is_sheaf_iff_is_sheaf_forget proetale_topology F (forget _),
  -- this is equivalent to the data above in a slightly re-arranged form
  rw [is_sheaf_iff_is_sheaf_of_type, (F ⋙ forget Ab).is_proetale_sheaf_of_types_tfae.out 0 2],
  -- now prove each direction by slightly rearranging the data
  split,
  { intros H α, exact H _ },
  { introsI H α _, exact H ⟨α⟩ }
end

/-!

## Condensed abelian groups.

To give a condensed abelian group in Lean is to give a pair of pieces of data: firstly
a presheaf of abelian groups on the category of profinite sets, and secondly a proof
that this presheaf is a sheaf for the proetale topology.

We write "$F$ is a condensed abelian group" as `F : Condensed.{0} Ab.{1}` in Lean.
-/

/- The objects of `Condensed.{0} Ab.{1}` are indeed just sheaves in `proetale_topology`.
The two components of a condensed abelian group `F`, the presheaf and the proof,
are called `F.1` and `F.2`.
 -/
example (F : Condensed.{0} Ab.{1}) : Profinite.{0}ᵒᵖ ⥤ Ab.{1} := F.1
example (F : Condensed.{0} Ab.{1}) : presheaf.is_sheaf proetale_topology F.1 := F.2

/-
Conversely, given a presheaf `F` and a proof `hF` that it's a sheaf for the proetale
topology, we can make a condensed abelian group using the `⟨F, hF⟩` syntax.
-/
example (F : Profinite.{0}ᵒᵖ ⥤ Ab.{1}) (hF : presheaf.is_sheaf proetale_topology F) :
  Condensed.{0} Ab.{1} := ⟨F, hF⟩

/-
This is a proof that the objects in the category of condensed abelian groups
are by definition sheaves of abelian groups for the topology `proetale_topology`
on the category of profinite types (or sets).
-/
example : Condensed.{0} Ab.{1} = Sheaf proetale_topology.{0} Ab.{1} := rfl
