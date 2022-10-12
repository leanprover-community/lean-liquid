import challenge

/-!

The main goal of this file is to discuss the definition of
condensed abelian groups which is used in this project.

As prerequisites, we also discuss continuous maps and the
category of profinite sets.

-/

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
example (f : C(X,Y)) : X → Y :=
f

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
`Profinite` denotes the category of profinite sets. Note that in Lean the category
of all sets is called `Type`.
-/
example := Profinite
example (X : Profinite) : Type := X

/-!
Any profinite set is a compact, Hausdorff, totally disconnected topological space.
-/
example (X : Profinite) : topological_space X := infer_instance
example (X : Profinite) : compact_space X := infer_instance
example (X : Profinite) : t2_space X := infer_instance
example (X : Profinite) : totally_disconnected_space X := infer_instance

/-!
Conversely, any topological space which is compact, Hausdorff and
totally disconnected is a profinite set.
The function `Profinite.of` is used to make an object of `Profinite`
from such a topological space.
-/
example (X : Type)
  [topological_space X]
  [compact_space X]
  [t2_space X]
  [totally_disconnected_space X] :
  Profinite :=
Profinite.of X

/-!
`Profinite` has a structure of a category. The morphisms are, by definition,
continuous maps.
-/
example (X Y : Profinite) : (X ⟶ Y) = C(X,Y) :=
-- True by definition
rfl

end profinite_sets

section proetale_topology

/-!
This section describes the Grothendieck topology on `Profinite` which is used in
our formalization of condensed mathematics.
We use the name `proetale_topology` for this Grothendieck topology.
-/
example : grothendieck_topology Profinite := proetale_topology

/-!
This example shows that the sheaf condition with respect to this Grothendieck topology,
for a presheaf of abelian groups on `Profinite`, is equivalent to the usual definition.
-/
example
-- Let `F` be a presheaf of abelian groups on `Profinite`.
  (F : Profiniteᵒᵖ ⥤ Ab) :
-- `F` is a sheaf for `proetale_topology`
  presheaf.is_sheaf proetale_topology F
-- if and only if the following condition holds:
  ↔
-- For any finite indexing type `α`,
  ∀ (α : Fintype)
-- profinite set `B`,
    (B : Profinite)
-- family of profinite sets `X` indexed by `α`
    (X : α → Profinite)
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
The category of condensed abelian groups is denoted by `Condensed Ab`.
As a type, `Condensed Ab` is defined to be the type of sheaves from `mathlib`.
-/
example : Condensed Ab = Sheaf proetale_topology Ab :=
-- true by definition
rfl

/-!
Any object of `Condensed Ab` yields a presheaf of abelian groups.
-/
example (F : Condensed Ab) : Profiniteᵒᵖ ⥤ Ab :=
F.1

/-!
The presheaf in the example above is indeed a sheaf.
-/
example (F : Condensed Ab) : presheaf.is_sheaf proetale_topology F.1 :=
F.2

/-!
Conversely, any presheaf of abelian groups on `Profinite`
(with the correct universe parameters) which is a sheaf for `proetale_topology`
yields an object of `Condensed Ab`.
-/
example (F : Profiniteᵒᵖ ⥤ Ab) (hF : presheaf.is_sheaf proetale_topology F) :
  Condensed Ab :=
⟨F,hF⟩

end proetale_topology
