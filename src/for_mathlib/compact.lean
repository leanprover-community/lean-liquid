import topology.subset_properties
import topology.algebra.monoid
-- minimize ↑ imports

variables {X Y Z α : Type*} [topological_space X]

-- move this
section for_mathlib

instance discrete_topology_bot : @discrete_topology α ⊥ :=
{ eq_bot := rfl }

lemma finite_of_is_compact_of_discrete [discrete_topology X] (s : set X) (hs : is_compact s) :
  s.finite :=
begin
  have := hs.elim_finite_subcover (λ x : X, ({x} : set X))
    (λ x, is_open_discrete _),
  simp only [set.subset_univ, forall_prop_of_true, set.Union_of_singleton] at this,
  rcases this with ⟨t, ht⟩,
  suffices : (⋃ (i : X) (H : i ∈ t), {i} : set X) = (t : set X),
  { rw this at ht, exact t.finite_to_set.subset ht },
  ext x,
  simp only [exists_prop, set.mem_Union, set.mem_singleton_iff, exists_eq_right', finset.mem_coe]
end

/-- If `(set.univ : set Y)` is finite then `Y` is a finite type. -/
noncomputable
def fintype_of_univ_finite (H : set.finite (set.univ : set Y)) :
  fintype Y :=
begin
  choose t ht using H.exists_finset,
  refine ⟨t, _⟩,
  simpa only [set.mem_univ, iff_true] using ht
end

/-- A compact discrete space is finite. -/
noncomputable
def fintype_of_compact_of_discrete [compact_space X] [discrete_topology X] :
  fintype X :=
fintype_of_univ_finite $ finite_of_is_compact_of_discrete _ compact_univ

end for_mathlib
