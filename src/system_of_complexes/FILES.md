# system_of_complexes

Most of these files are not about arbitrary complexes, but about a system of complexes of
seminormed groups. By a "system" we mean a collection of complexes of seminormed groups
indexed by the reals which are at least some fixed real c₀, and equipped with restriction
maps. A good reference for this is section 4 of the blueprint.

## Files

- `complex.lean` : contains basic definitions of complexes, maps between complexes, and
  what it means for two maps to be homotopic.
- `basic.lean` : systems of complexes of seminormed groups, admissible systems
  and concepts of bounded exactness (see Definition 9.3 of
  Scholze's `analytic.pdf`, or Definitions 4.1 to 4.4 of the blueprint).
- `completion.lean` : completion of a complex, and a technical lemma about how
  one kind of bounded exactness implies another for complexes of complete seminormed groups.
- `double.lean` : systems of double complexes of seminormed groups, used in
  Proposition 9.6 of `analytic.pdf`.
- `truncate.lean` truncates a complex of seminormed groups (and a system of complexes)
  by sending `C₀ → C₁ → C₂ → ...` to `(coker (C₀ → C₁)) → C₂ → C₃ → ...`

- `rescale.lean` (imports `rescale.normed_group`) : rescales the norms on
  a system of complexes by a constant factor.
