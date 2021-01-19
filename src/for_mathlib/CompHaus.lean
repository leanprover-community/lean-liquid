import topology.category.CompHaus

namespace CompHaus

variables (X : Type*) [topological_space X] [compact_space X] [t2_space X]

def of : CompHaus :=
{ to_Top := Top.of X,
  is_compact := ‹_›,
  is_hausdorff := ‹_› }

@[simp] lemma coe_of : (CompHaus.of X : Type _) = X := rfl

end CompHaus
#lint- only unused_arguments
