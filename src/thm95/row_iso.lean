import thm95.double_complex

/-!
# A complex canonically isomorphic to `row 1` of the double complex

We have
```
lemma double_complex.row_one :
  (double_complex BD c' r r' V Λ M N).row 1 =
  BD.system c' r V r'
    (Hom (polyhedral_lattice.conerve.obj
    (PolyhedralLattice.diagonal_embedding Λ N) 1) M) := rfl
```

We want to "rewrite" this row in such a way that it is the target
of the homotopies that will be constructed formally from `BD.homotopy`.

This means that we need to multiply `BD` by `N`,
and then take the system associated with `rescale N (Hom Λ M)`.

We need the following isomorphisms

* `BD.system M^N = (BD.mul N).system M` (`BD.mul` isn't yet defined)
* `Hom (rescale N (Λ^N)) M = (rescale N (Hom Λ M)^N` (2 steps?)
* `polyhedral_lattice.conerve.obj (PolyhedralLattice.diagonal_embedding Λ N) 1 = rescale N (Λ^N)`

-/
