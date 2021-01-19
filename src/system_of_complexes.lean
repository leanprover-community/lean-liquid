import algebra.homology.chain_complex

import normed_group.NormedGroup
import facts

universe variables v u
noncomputable theory
open opposite category_theory
open_locale nnreal

/-!
# Systems of complexes of normed abelian groups

In this file we define systems of complexes of normed abelian groups,
along the lines of Definition 9.3 of [Analytic].

## Main declarations

* `system_of_complexes`: a system of complexes of normed abelian groups.
* `is_bdd_exact_for_bdd_degree_above_idx`: an exactness criterion for such systems,
    requiring a suitable interplay between the norms and the algebraic properties of the system.
* `admissible`: such a system is *admissible* if all maps that occur in the system
    are norm-nonincreasing.
-/

-- TODO: at some point we can abstract the following definition over `NormedGroup` and `ℝ≥0`.
-- But I don't think that is relevant for this project.

/-- A system of complexes of normed abelian groups, indexed by `ℝ≥0`.
See also Definition 9.3 of [Analytic].

Implementation detail: `cochain_complex` assumes that the complex is indexed by `ℤ`,
whereas we are interested in complexes indexed by `ℕ`.
We therefore set all objects indexed by negative integers to `0`, in our use case. -/
@[derive category_theory.category]
def system_of_complexes := ℝ≥0ᵒᵖ ⥤ (cochain_complex NormedGroup)

namespace system_of_complexes

variables (C : system_of_complexes)

/-- `C.X c i` is the object $C_c^i$ in a system of complexes `C`. -/
def X (c : ℝ≥0) (i : ℤ) : NormedGroup :=
(C.obj $ op c).X i

/-- `C.res` is the restriction map `C.X c' i ⟶ C.X c i` for a system of complexes `C`,
and nonnegative reals `c ≤ c'`. -/
def res {c' c : ℝ≥0} {i : ℤ} [h : fact (c ≤ c')] :
  C.X c' i ⟶ C.X c i :=
(C.map (has_hom.hom.op ⟨⟨h⟩⟩)).f i

/-- `C.d` is the differential `C.X c i ⟶ C.X c (i+1)` for a system of complexes `C`. -/
def d {c : ℝ≥0} {i : ℤ} :
  C.X c i ⟶ C.X c (i+1) :=
(C.obj $ op c).d i

/-- Convenience definition:
The identity morphism of an object in the system of complexes
when it is given by different indices that are not
definitionally equal. -/
def congr {c c' : ℝ≥0} {i i' : ℤ} (hc : c = c') (hi : i = i') :
  C.X c i ⟶ C.X c' i' :=
eq_to_hom $ by { subst hc, subst hi }

/-
Peter Scholze:
(Note that `k` plays a strange double role in Definition 9.3,
quantifying both the depth of restriction and the increase in norm;
somehow it was not necessary to disentangle this for the argument,
so I used one variable for two distinct things.
Only one of them really needs to be `≥1`,
the one parametrizing the depth of restriction.
If one wants to get good estimates at some point,
it may be useful to introduce two parameters here.)

https://leanprover.zulipchat.com/#narrow/stream/266894-liquid/topic/bounded.20exactness/near/220823654
-/

/-- `is_bdd_exact_for_bdd_degree_above_idx k m c₀` is a predicate on systems of complexes.

A system of complexes `C` is *`≤ k`-exact in degrees `≤ m` for `c ≥ c₀'`*
if the following condition is satisfied:
For all `c ≥ c₀'` and all `x : C.X (k * c) i` with `i ≤ m` there is some `y : C.X c (i-1)`
(which is defined to be `0` when `i = 0`) such that `∥(C.res x) - (C.d y)∥ ≤ k * ∥C.d x∥`.

See Definition 9.3 of [Analytic].

Implementation details:
* Because our chain complexes are indexed by `ℤ` instead of `ℕ`,
  and we make sure that objects indexed by negative integers are `0`,
  we automatically take care of the parenthetical condition about `i = 0`.
* The original text bounds `i` as `i ≤ m`, and then requires `y : C.X c (i-1)`.
  We change this to `i < m` and `y : C.X c i`, because this has better definitional properties.
  (This is a hack around an inconvenience known as dependent type theory hell.) -/
def is_bdd_exact_for_bdd_degree_above_idx
  (k : ℝ≥0) (m : ℤ) (c₀' : ℝ≥0) [hk : fact (1 ≤ k)] : Prop :=
∀ c ≥ c₀', ∀ i < m,
∀ x : C.X (k * c) (i+1),
∃ y : C.X c i, ∥(C.res x) - (C.d y)∥ ≤ k * ∥C.d x∥

/-- A system of complexes is *admissible*
if all the differentials and restriction maps are norm-nonincreasing.

See Definition 9.3 of [Analytic]. -/
structure admissible (C : system_of_complexes) : Prop :=
(differential_norm_noninc : ∀ c i, normed_group_hom.bound_by (C.d : C.X c i ⟶ C.X c (i+1)) 1)
(restriction_norm_noninc : ∀ c' c i h, normed_group_hom.bound_by (@res C c' c i h) 1)

end system_of_complexes
#lint- only unused_arguments
