# breen_deligne

In this directory the theory of section 1 of the blueprint is formalised.
A universal map from exponent `m` to `n` is a collection of
group homomorphisms `φ_A : ℤ[A^m] → ℤ[A^n]` for any abelian group `A` which
are functorial in `A` in the obvious sense. These things are formalised
a finite formal ℤ-linear combinations of integer `n × m` matrices in
`universal_map.lean` and the proof that they correspond to functorial
collections of group homomorphisms is in `functorial_map.lean`. An example
of a complex of such maps is given in `eg.lean`. The file `suitable.lean`
defines the notions of "suitability" explained in definitions 1.11-1.13
of the blueprint. Everything is ported to a category-theoretic language
in `category.lean`.

Note that right now this directory does _not_ contain a proof of the
Breen-Deligne theorem, either in the traditional form which allows
ℤ[A^m1]⊕ℤ[A^m2] etc, or in the stronger form which demands that every
object in the resolution is of the form ℤ[A^m].

## TODO

Prove the Breen-Deligne theorem! However this is rather
a long-term goal at the minute, and is not something
which is being worked on.
