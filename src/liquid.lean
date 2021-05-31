import thm95
import statement

/-!
# Liquid Tensor Experiment

This file is the entry point for this project.
The first goal of the Liquid Tensor Experiment
is to formalize a theorem by Clausen and Scholze stated below,
namely a mix of Theorem 9.4 and Theorem 9.5 of
[Analytic]: http://www.math.uni-bonn.de/people/scholze/Analytic.pdf

**How to browse this project? See `README.md` in the root of the repository.**

We will now state the main theorem.

First we need to fix a package of data corresponding to the Breen--Deligne resolution.
If you don't know the Breen--Deligne resolution, don't worry,
we'll explain more about how to find out more about it below.
Once we have fixed this data, we can state the theorem.
-/

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.

open category_theory ProFiltPseuNormGrpWithTinv polyhedral_lattice opposite

variables (BD : breen_deligne.package)
variables (c_ : ℕ → ℝ≥0)  -- implicit constants, chosen once and for all
                          -- see the sentence after that statement of Thm 9.5

/-- A mix of Theorems 9.4 and 9.5 in [Analytic] -/
theorem first_target (r r' : ℝ≥0)
  [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]
  [BD.data.very_suitable r r' c_] [∀ (i : ℕ), fact (0 < c_ i)] :
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : SemiNormedGroup.{0}) [normed_with_aut r V],
    ​((BD.data.system c_ r V r').obj (op $ of r' (Mbar r' S))).is_weak_bounded_exact k K m c₀ :=
begin
  intro m,
  obtain ⟨k, K, hk, H⟩ := thm95'' BD r r' c_ m,
  obtain ⟨c₀, H⟩ := H ℤ,
  use [k, K, hk, c₀],
  introsI S hS V hV,
  specialize H S V,
  let i := (BD.data.system c_ r V r').map_iso (HomZ_iso (of r' $ Mbar r' S)).op,
  refine H.of_iso i.symm _,
  intros c n,
  rw ← system_of_complexes.apply_hom_eq_hom_apply,
  apply SemiNormedGroup.iso_isometry_of_norm_noninc;
  apply breen_deligne.data.complex.map_norm_noninc
end

/-!
## On the statement

Most of the theorem should be fairly readable.
We will now briefly explain some of the more peculiar syntax.
The proof reduces to `thm95`, which is not proven yet. We are working on it!

* `[BD.suitable c_]` assumes that the nonnegative reals `c_ i` satisfy some suitable conditions
  with respect to the package of Breen--Deligne data `BD`.
* `[fact (0 < r)]` records the "fact" `0 < r` as an assumption to whatever comes later.
* `(S : Type) [fintype S]` is Lean's way of saying "`S` is a finite set".
  See also the "Brief note on type theory" in `README.md`.
* `[normed_with_aut r V]` adds the assumption that `V` is endowed with an automorphism `T`
  that scales elements `v` of `V` by the positive scalar `r`: `∥T(v)∥ = r * ∥v∥`.
* `Mbar_system` is the system of complexes of seminormed groups
  occuring in Theorems 9.4/9.5 of [Analytic].
* `is_bounded_exact` is the assertion that a system of complexes
  of seminormed groups satisfies a suitable exactness criterion of being
  `≤ k`-exact in degrees `≤ m` for `c ≥ c₀` (where `c` is an index to the system of complexes).
-/

example (r r' : ℝ≥0)
  [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]
  [BD.data.very_suitable r r' c_] [∀ (i : ℕ), fact (0 < c_ i)] :
  first_target_stmt BD c_ r r' :=
first_target BD c_ r r'
