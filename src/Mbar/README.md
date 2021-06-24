# Mbar

In this directory we define an example of a
profinitely filtered pseudo-normed group with $T^{-1}$-action.
This example plays a central role in the statement of `first_target`.

The definition is as follows:
```lean
/-- `Mbar r' S` is the set of power series
`F_s = ∑ a_{s,n}T^n ∈ Tℤ[[T]]` such that `∑_{s,n} |a_{s,n}|r'^n` converges -/
structure Mbar (r' : ℝ≥0) (S : Type u) [fintype S] :=
(to_fun      : S → ℕ → ℤ)
(coeff_zero' : ∀ s, to_fun s 0 = 0)
(summable'   : ∀ s, summable (λ n, (↑(to_fun s n).nat_abs * r' ^ n)))
```

This is naturally a pseudo-normed group,
filtered by those power series for which the sum converges to a number `≤ c`.
We then need to perform some work to put a profinite topology on these filtration sets.

# Files

- `basic.lean`: Definition of `ℳ-bar_{r'}(S)` and the T⁻¹-action
- `bounded.lean`: Natural finite quotients of `ℳ-bar_{r'}(S)_{≤c}`
- `Mbar_le.lean`: The subtype `ℳ-bar_{r'}(S)_{≤c}` of `ℳ-bar_{r'}(S)` and its profinite topology
- `pseudo_normed_group.lean`: Profinitely filtered pseudo-normed group structure with T⁻¹-action
