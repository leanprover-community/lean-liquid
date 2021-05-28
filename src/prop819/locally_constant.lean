import locally_constant.SemiNormedGroup
import category_theory.arrow
import for_mathlib.Profinite.fibprod
import for_mathlib.Profinite.arrow_limit

noncomputable theory

open category_theory

universe u

variables (n : ℕ) (F : arrow Profinite.{u}) (M : SemiNormedGroup.{u}) (surj : function.surjective F.hom)

open SemiNormedGroup opposite Profinite

-- This has moved.
/-
/-- The functor sending a discrete quotient of F.left to the
n-fold fibered product of the quotient of F induced by the quotient.
-/
abbreviation FPR : discrete_quotient F.left ⥤ Profinite :=
arrow_diagram F surj ⋙ fibprod n

/-- A cone associated to FPR. -/
abbreviation FPR_cone : limits.cone (FPR n F surj) :=
(fibprod n).map_cone $ arrow_cone _ _

/--
The assertion that a loccally constant map on the fibered product
arises from some discrete quotient via the `make_arrow` construction.
-/
lemma exists_locally_constant_fibprod
  (f : (LocallyConstant.obj M).obj (op $ (fibprod n).obj F)) :
  ∃ (S : discrete_quotient F.left)
    (g : (LocallyConstant.obj M).obj (op $ (FPR n F surj).obj S)),
    (LocallyConstant.obj M).map ((FPR_cone n F surj).π.app S).op g = f := by admit

/--
The assertion that if a locally constant function becomes trivial in the limit,
then it becomes trivial at some finite level.
-/
lemma locally_constant_eq_zero (S : discrete_quotient F.left)
  (f : (LocallyConstant.obj M).obj (op $ (FPR n F surj).obj S))
  (cond : (LocallyConstant.obj M).map ((FPR_cone n F surj).π.app S).op f = 0) :
  ∃ (T : discrete_quotient F.left) (h : T ≤ S),
    (LocallyConstant.obj M).map ((FPR n F surj).map $ hom_of_le h).op f = 0 := by admit
-/
