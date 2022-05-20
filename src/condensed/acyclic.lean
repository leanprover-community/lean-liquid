import for_mathlib.derived.example
import for_mathlib.Cech.homotopy
import for_mathlib.acyclic

import condensed.projective_resolution
.

noncomputable theory

universes u

open category_theory category_theory.limits homotopy_category opposite
open function (surjective)

namespace condensed

variable (M : Condensed.{u} Ab.{u+1})

abbreviation HH (i : ℤ) (S : Profinite.{u}) (M : Condensed.{u} Ab.{u+1}) :=
((Ext' i).obj (op $ (CondensedSet_to_Condensed_Ab).obj $ Profinite.to_Condensed S)).obj M

def acyclic_of_exact.IH (n : ℤ) : Prop := ∀ S, ∀ i > 0, i ≤ n → is_zero (HH i S M)

lemma acyclic_of_exact.induction_step
  (h : ∀ (F : arrow Profinite.{u}) (surj : function.surjective F.hom),
    ∀ i, is_zero
    (((((cosimplicial_object.augmented.whiskering _ _).obj M.val).obj
      F.augmented_cech_nerve.right_op).to_cocomplex).homology i))
  (n : ℤ) (hn : acyclic_of_exact.IH M n) :
  acyclic_of_exact.IH M (n+1) :=
begin
  intros S i h1 h2,
  -- use `arrow.conerve_to_cocomplex_homology_is_zero`
  sorry
end

lemma acyclic_of_exact
  (h : ∀ (F : arrow Profinite.{u}) (surj : function.surjective F.hom),
    ∀ i, is_zero
    (((((cosimplicial_object.augmented.whiskering _ _).obj M.val).obj
      F.augmented_cech_nerve.right_op).to_cocomplex).homology i))
  (S : Profinite.{u}) :
  ∀ i > 0, is_zero (HH i S M)  :=
begin
  intros i hi,
  suffices : acyclic_of_exact.IH M i,
  { apply this S i hi le_rfl, },
  apply int.induction_on' i 0; clear hi i S,
  { intros S i h1 h2, exfalso, exact h2.not_lt h1 },
  { intros k hk, apply acyclic_of_exact.induction_step M h, },
  { rintros k hk aux S i h1 h2, exfalso, linarith only [hk, h1, h2] }
end

end condensed
