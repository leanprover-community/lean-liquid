# locally_constant

The files in this directory set up the theory of locally constant maps
from profinite spaces to normed groups (such a space inherits
a normed group structure via the sup norm). It also sets up the theory
of completions of normed groups, and hence the definition "M-hat"
in definition 8.18 of `analytic.pdf` .

- `analysis.lean`: Locally constant maps from a compact top space to a normed group are a normed
  group.
- `NormedGroup.lean`: category-theoretic reformulation.
- `Vhat.lean`: completions of normed groups, and the LCC bifunctor sending a normed abelian
  group `V` and a profinite space `S` to `V-hat(S)`, the completion of the locally constant
  functions S -> V.
