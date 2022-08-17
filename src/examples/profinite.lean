import challenge

/-!

This file explains the structure of profinite sets.

-/

/-
`Profinite.{0}` denotes the type of profinite sets whose underlying type
lives in `Type = Type 0`.
-/
example : Type 1 := Profinite.{0}
example (X : Profinite.{0}) : Type := X

/-
Any profinite set is a compact, Hausdorff, totally disconnected topological space.
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
Profinite.of X

/-
The morphisms in the category of profinite sets are just continuous maps.
-/
example (X Y : Profinite.{0}) : (X ⟶ Y : Type) = C(X,Y) := rfl
