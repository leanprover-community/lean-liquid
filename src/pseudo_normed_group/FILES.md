# pseudo_normed_group

- `basic`: contains definitions and basic properties of pseudo-normed groups. See
  definition 2.1 of the blueprint.
- `category`: Defines the category of profinite pseudo-normed groups, and the category of
  profinitely filtered pseudo-normed groups equipped with an action of T⁻¹.
- `profinitely_filtered.lean`: definition of a profinitely_filtered_pseudo_normed_group.
- `with_Tinv.lean`: The definition of `profinitely_filtered_pseudo_normed_group_with_Tinv`.

- `breen_deligne.lean`: the definition of the action of a basic universal map
  on powers of a pseudo-normed group and related types.
- `FiltrationPow.lean`: the construction of the map `M_c₁^m → M_c₂^n` induced by
  a (c₁, c₂)-suitable φ.
- `LC.lean` and `CLC.lean` build up to the functor sending a profinitely-filtered `T⁻¹`-module `M`
   to `V-hat((M_c)^n)`, the normed group completion of the locally constant functions
   from `M_c^n` to `V`.
- `Tinv.lean`: the construction of the `T⁻¹`-invariant elements of `V-hat((M_c)^n)`, if
  `V` and `M` both have actions of `T⁻¹`
- `system_of_complexes.lean`: the construction of the system of complexes used
  in Theorem 9.4.

## TODO

homotopy.lean
