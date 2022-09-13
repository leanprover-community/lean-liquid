import challenge

open category_theory category_theory.limits opposite
open_locale liquid_tensor_experiment

section continuous_maps

/-!
This section describes the type `C(X,Y)` of continuous maps from `X` to `Y`.
-/

/-!
Let `X` and `Y` be topological spaces.
-/
variables {X Y : Type*} [topological_space X] [topological_space Y]

/-!
Any `f : C(X,Y)` can be thought of as a function from `X` to `Y`.
-/
example (f : C(X,Y)) : X → Y := f

/-!
A term `f` of `C(X,Y)` is continuous, when considered as a function `X → Y`.
-/
example (f : C(X,Y)) : continuous f :=
f.continuous

/-!
Conversely, any continuous function `X → Y` yields an element of `C(X,Y)`.
-/
example (f : X → Y) (hf : continuous f) : C(X,Y) :=
⟨f,hf⟩

end continuous_maps

section profinite_sets

/-!
In this section, we discuss the category of profinite sets.
-/

/-!
`Profinite.{0}` denotes the type of profinite sets whose underlying type
lives in `Type = Type 0`.
-/
example : Type 1 := Profinite.{0}
example (X : Profinite.{0}) : Type := X

/-!
Any profinite set is a compact, Hausdorff, totally disconnected topological space.
-/
example (X : Profinite.{0}) : topological_space X := infer_instance
example (X : Profinite.{0}) : compact_space X := infer_instance
example (X : Profinite.{0}) : t2_space X := infer_instance
example (X : Profinite.{0}) : totally_disconnected_space X := infer_instance

/-!
Conversely, any topological space which is compact, Hausdorff and
totally disconnected is a profinite set.
The function `Profinite.of` is used to make an object of `Profinite.{0}`
from such a topological space.
-/
example (X : Type)
  [topological_space X]
  [compact_space X]
  [t2_space X]
  [totally_disconnected_space X] :
  Profinite.{0} :=
Profinite.of X

/-
`Profinite.{0}` has a structure of a category, where morphisms are, by definition,
continuous maps.
-/
example (X Y : Profinite.{0}) : (X ⟶ Y : Type) = C(X,Y) := rfl

end profinite_sets

section proetale_topology

/-!
This section describes the Grothendieck topology on `Profinite.{0}` which is used in
our formalization of condensed mathematics.
We use the name `proetale_topology` for this Grothendieck topology.
-/
example : grothendieck_topology Profinite.{0} := proetale_topology

/-!
This example shows that the sheaf condition with respect to this Grothendieck topology,
for a presheaf of abelian groups on `Profinite.{0}`, is equivalent to the usual definition.
-/
example
-- Let `F` be a presheaf of abelian groups on `Profinite.{0}`.
  (F : Profinite.{0}ᵒᵖ ⥤ Ab.{1}) :
-- `F` is a sheaf for `proetale_topology`
  presheaf.is_sheaf proetale_topology F
-- if and only if the following condition holds:
  ↔
-- For any finite indexing type `α`,
  ∀ (α : Fintype.{0})
-- profinite set `B`,
    (B : Profinite.{0})
-- family of profinite sets `X` indexed by `α`
    (X : α → Profinite.{0})
-- which map to `B` with a family of maps `π`,
    (π : Π i, X i ⟶ B)
-- such that `π` is jointly surjective,
    (hπ : ∀ b : B, ∃ i (x : X i), π i x = b)
-- and all families of elements `x i : F (op $ X i)`,
    (x : Π i, F (op $ X i))
-- which are compatible on pullbacks `X i ×_{B} X j`
    (hx : ∀ i j : α,
      F.map (pullback.fst : pullback (π i) (π j) ⟶ X i).op (x i) =
      F.map (pullback.snd : pullback (π i) (π j) ⟶ X j).op (x j)),
-- there is a unique `s : F (op B)`
    ∃! s : F (op B),
-- which restricts to `x i` over `X i` for all `i`.
      ∀ i, F.map (π i).op s = x i :=
begin
  rw presheaf.is_sheaf_iff_is_sheaf_forget proetale_topology F (forget _),
  rw [is_sheaf_iff_is_sheaf_of_type, (F ⋙ forget Ab).is_proetale_sheaf_of_types_tfae.out 0 2],
  split,
  { intros H α, exact H _ },
  { introsI H α _, exact H ⟨α⟩ }
end

/-!
The category of condensed abelian groups is denoted by `Condensed.{0} Ab.{1}`.
The objects of `Condensed.{0} Ab.{1}` are indeed just sheaves for `proetale_topology`.
-/
example (F : Condensed.{0} Ab.{1}) : Profinite.{0}ᵒᵖ ⥤ Ab.{1} := F.1
example (F : Condensed.{0} Ab.{1}) : presheaf.is_sheaf proetale_topology F.1 := F.2

/-!
Conversely, any presheaf (with the correct universe levels)
satisfying the sheaf condition can be considered as an object
of `Condensed.{0} Ab.{1}`.
-/
example (F : Profinite.{0}ᵒᵖ ⥤ Ab.{1}) (hF : presheaf.is_sheaf proetale_topology F) :
  Condensed.{0} Ab.{1} := ⟨F,hF⟩

/-!
As a type, `Condensed.{0} Ab.{1}` is defined to be the type of sheaves from `mathlib`.
-/
example : Condensed.{0} Ab.{1} = Sheaf proetale_topology.{0} Ab.{1} := rfl

end proetale_topology
