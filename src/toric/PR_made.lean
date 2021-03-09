import algebra.regular
import topology.separation

-- PR #6570
-- branch adomani_discrete_topology_trans
/-- Let `X` be a topological space and let `s, t ⊆ X` be two subsets.  If there is an inclusion
`t ⊆ s`, then the topological space structure on `t` induced by `X` is the same as the one
obtained by the induced topological space structure on `s`. -/
lemma topological_space.subset_trans {X : Type*} [tX : topological_space X]
  {s t : set X} (ts : t ⊆ s) :
  (subtype.topological_space : topological_space t) =
    (subtype.topological_space : topological_space s).induced (set.inclusion ts) :=
begin
  change tX.induced ((coe : s → X) ∘ (set.inclusion ts)) =
    topological_space.induced (set.inclusion ts) (tX.induced _),
  rw ← induced_compose,
end

/-- I imagine that this lemma characterizes discrete topological spaces as those having
every as a neighbourhood of its points. -/
lemma discrete_topology_iff_nhds {X : Type*} [topological_space X] :
  discrete_topology X ↔ (nhds : X → filter X) = pure :=
begin
  split,
  { introI hX,
    exact nhds_discrete X },
  { intro h,
    constructor,
    apply eq_of_nhds_eq_nhds,
    simp [h, nhds_bot] }
end

/-- The topology pulled-back under an inclusion `f : X → Y` from the discrete topology (`⊥`) is the
discrete topology.
This version does not assume the choice of a topology on either the source `X`
nor the target `Y` of the inclusion `f`. -/
lemma induced_bot {X Y : Type*} {f : X → Y} (hf : function.injective f) :
  topological_space.induced f ⊥ = ⊥ :=
eq_of_nhds_eq_nhds (by simp [nhds_induced, ← set.image_singleton, hf.preimage_image, nhds_bot])

/-- The topology induced under an inclusion `f : X → Y` from the discrete topological space `Y`
is the discrete topology on `X`. -/
lemma discrete_topology_induced {X Y : Type*} [tY : topological_space Y] [discrete_topology Y]
  {f : X → Y} (hf : function.injective f) : @discrete_topology X (topological_space.induced f tY) :=
begin
  constructor,
  rw discrete_topology.eq_bot Y,
  exact induced_bot hf
end

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.  -/
lemma discrete_topology.of_subset {X : Type*} [topological_space X] {s t : set X}
  (ds : discrete_topology s) (ts : t ⊆ s) :
  discrete_topology t :=
begin
  rw [topological_space.subset_trans ts, ds.eq_bot],
  exact {eq_bot := induced_bot (set.inclusion_injective ts)}
end



-- merged PR
variables {R : Type*} {a : R}

/-- A left-regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
lemma is_left_regular.ne_zero [mul_zero_class R] [nontrivial R] (la : is_left_regular a) : a ≠ 0 :=
begin
  rintro rfl,
  rcases exists_pair_ne R with ⟨x, y, xy⟩,
  refine xy (la _),
  rw [zero_mul, zero_mul]
end

/-- A right-regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
lemma is_right_regular.ne_zero [mul_zero_class R] [nontrivial R] (ra : is_right_regular a) :
  a ≠ 0 :=
begin
  rintro rfl,
  rcases exists_pair_ne R with ⟨x, y, xy⟩,
  refine xy (ra (_ : x * 0 = y * 0)),
  rw [mul_zero, mul_zero]
end

/-- A regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
lemma is_regular.ne_zero [nontrivial R] [mul_zero_class R] (la : is_regular a) : a ≠ 0 :=
la.left.ne_zero

/-- In a non-trivial integral domain, an element is regular iff it is non-zero. -/
lemma is_regular_iff_ne_zero [nontrivial R] [cancel_monoid_with_zero R] : is_regular a ↔ a ≠ 0 :=
⟨is_regular.ne_zero, is_regular_of_ne_zero⟩
