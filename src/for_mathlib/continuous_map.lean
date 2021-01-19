import topology.continuous_map

namespace continuous_map

variables {X Y : Type*} [topological_space X] [topological_space Y]

@[simp] lemma coe_mk (f : X → Y) (h : continuous f) :
  ⇑(⟨f, h⟩ : continuous_map X Y) = f := rfl

end continuous_map
#lint- only unused_arguments def_lemma doc_blame
