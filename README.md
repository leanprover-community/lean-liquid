# Liquid Tensor Experiment

![](https://github.com/leanprover-community/lean-liquid/workflows/continuous%20integration/badge.svg?branch=master)

A project to formalize Theorem 9.5 of Scholze--Clausen [Analytic.pdf]

## The statement

The statement can be found in [`src/liquid.lean`](https://github.com/leanprover-community/lean-liquid/blob/master/src/liquid.lean#L32)

```lean
theorem main [BD.suitable c']
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)] :
  ∀ m : ℕ,
  ∃ (k : ℝ≥0) [fact (1 ≤ k)],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : NormedGroup) [normed_with_aut r V],
  by exactI (Mbar_system V S r r' BD c').is_bdd_exact_for_bdd_degree_above_idx k m c₀ :=
sorry
```

See [`src/liquid.lean`](https://github.com/leanprover-community/lean-liquid/blob/master/src/liquid.lean#43)
for details on how to read this statement.

## How to browse this repository

Under construction.
We will add some useful instructions soon.
We have just finished the formalisation of the *statement* (not the proof!) of Theorem 9.5,
and we are currently busy with cleaning up the code.

## Source reference

[Analytic.pdf]: http://www.math.uni-bonn.de/people/scholze/Analytic.pdf
