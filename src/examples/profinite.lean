import challenge

/-!

This file explains the structure of profinite sets.

-/

open category_theory opposite
open_locale liquid_tensor_experiment

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

/-
The `proetale_topology` is the Grothendieck topology on `Profinite.{0}` which is used in
condensed mathematics.
-/
example : grothendieck_topology Profinite.{0} := proetale_topology

/-
This example shows that the sheaf condition with respect to this Grothendieck topology,
for a presheaf of abelian groups on `Profinite.{0}`, is equivalent to the usual definition.
-/
example (F : Profinite.{0}ᵒᵖ ⥤ Ab.{1}) :
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
  rw presheaf.is_sheaf_iff_is_sheaf_forget proetale_topology F (forget _),
  rw [is_sheaf_iff_is_sheaf_of_type, (F ⋙ forget Ab).is_proetale_sheaf_of_types_tfae.out 0 2],
  split,
  { intros H α, exact H _ },
  { introsI H α _, exact H ⟨α⟩ }
end

/- The objects of `Condensed.{0} Ab.{1}` are indeed just sheaves in `proetale_topology`. -/
example (F : Condensed.{0} Ab.{1}) : Profinite.{0}ᵒᵖ ⥤ Ab.{1} := F.1
example (F : Condensed.{0} Ab.{1}) : presheaf.is_sheaf proetale_topology F.1 := F.2

example (F : Profinite.{0}ᵒᵖ ⥤ Ab.{1}) (hF : presheaf.is_sheaf proetale_topology F) :
  Condensed.{0} Ab.{1} := ⟨F,hF⟩

example : Condensed.{0} Ab.{1} = Sheaf proetale_topology.{0} Ab.{1} := rfl
