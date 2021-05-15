# normed_group

This directory contains a development of the theory of normed abelian (additive) groups.

## Files

- `controlled_exactness.lean`: the proof of Proposition 8.17 of `analytic.pdf`,
  stating that the completion of a complex with some boundedness properties
  also has some boundedness properties.
- `normed_with_aut.lean`: Definition 8.13 of `analytic.pdf` -- a normed
  group with an action of `T` which scales norms by a factor `r`.
- `SemiNormedGroup.lean`: The category of seminormed groups and continuous group
  homomorphisms, including an API for cokernels.
- `pseudo_normed_group.lean`: The construction of a pseudo-normed group from
  a seminormed group.
