# polyhedral_lattice

A polyhedral lattice is a finite free ℤ-module equipped with a norm (making it into
a normed group) which has a certain combinatorial shape (the unit ball of the associated
Banach space obtained by tensoring up to the reals is a polyhedron). We appear to have
dropped the "rational" assumption present in `analytic.pdf`.

A morphism of polyhedral lattices is defined to be norm-nonincreasing.

Files in this directory (in import order). The following files just essentially build
on what is (or should be) in mathlib:

- `basic.lean` : basic definition of polyhedral lattices.
- `int.lean` : the integers with its usual norm are a polyhedral lattice.
- `category.lean` : constructs the category of polyhedhral lattices.
- `finsupp.lean` : if Λ is a polyhedral lattice then so is Hom(ι, Λ) for ι finite.
- `cech.lean` : the Cech conerve of a morphism of polyhedral lattices.
- `cosimplicial.lean` : The cosimplicial object in the category of polyhedral lattices
  associated to the Cech conerve.
- `direct_sum.lean` : A finite direct sum of polyhedral lattices is a normed group
  (the proof that it's a polyhedral lattice is missing, and possibly not needed).
- `rescale.lean` : rescaling the norm on a polyhedral lattice by a positive real factor
  gives a polyhedral lattice.
- `topology.lean` : right now an empty file (and it might remain that way).

The last two files need some of the theory of normed groups and pseudo normed groups,
defined in `normed_group` and `pseudo_normed_group`.

- `pseudo_normed_group.lean` : If M is a pseudo-normed group with T⁻¹ then so is Hom(Λ, M).
- `Hom.lean` : A category-theoretic version: Hom(Λ, -) is a functor (and it's isomorphic
  to the identity functor when Λ = ℤ).
