import topology.discrete_quotient

namespace discrete_quotient

variables {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  {f : X → Y} {g : Y → Z} (hf : continuous f) (hg : continuous g)

/-- Map a discrete quotient along a continuous function. -/
def map {I : discrete_quotient X} {J : discrete_quotient Y}
  (cond : I ≤ J.comap hf) : I → J := quotient.map' f (by tauto)

lemma map_continuous {I : discrete_quotient X} {J : discrete_quotient Y}
  (cond : I ≤ J.comap hf) : continuous (map hf cond) := continuous_of_discrete_topology

@[simp]
lemma of_le_map {I : discrete_quotient X} {J1 J2 : discrete_quotient Y}
  (cond1 : J1 ≤ J2) (cond2 : I ≤ J1.comap hf) :
(of_le cond1) ∘ (map hf cond2) = map hf (by tauto) := by tidy

@[simp]
lemma of_le_map_apply {I : discrete_quotient X} {J1 J2 : discrete_quotient Y}
  (cond1 : J1 ≤ J2) (cond2 : I ≤ J1.comap hf) (i : I) :
of_le cond1 (map hf cond2 i) = map hf (by tauto) i := by tidy

@[simp]
lemma map_of_le {I1 I2 : discrete_quotient X} {J : discrete_quotient Y}
  (cond1 : I1 ≤ I2) (cond2 : I2 ≤ J.comap hf) :
(map hf cond2) ∘ (of_le cond1) = map hf (by tauto) := by tidy

@[simp]
lemma map_of_le_apply {I1 I2 : discrete_quotient X} {J : discrete_quotient Y}
  (cond1 : I1 ≤ I2) (cond2 : I2 ≤ J.comap hf) (i : I1) :
map hf cond2 (of_le cond1 i) = map hf (by tauto) i := by tidy

@[simp]
lemma map_id {I J : discrete_quotient X} (cond : I ≤ J) :
map (continuous_id : continuous (id : X → X)) cond = of_le cond := by tidy

@[simp]
lemma map_comp {I : discrete_quotient X} {J : discrete_quotient Y} {K : discrete_quotient Z}
  (cond1 : I ≤ J.comap hf) (cond2 : J ≤ K.comap hg) :
map (continuous.comp hg hf) (by tauto) = map hg cond2 ∘ map hf cond1 := by tidy

@[simp]
lemma map_comp_apply {I : discrete_quotient X} {J : discrete_quotient Y} {K : discrete_quotient Z}
  (cond1 : I ≤ J.comap hf) (cond2 : J ≤ K.comap hg) (i : I) :
map (continuous.comp hg hf) (by tauto) i = map hg cond2 (map hf cond1 i) := by tidy

@[simp]
lemma comap_id (I : discrete_quotient X) :
I.comap continuous_id = I := by tidy

@[simp]
lemma comap_comp {I : discrete_quotient Z} :
I.comap (continuous.comp hg hf) = (I.comap hg).comap hf := by tidy

@[simp]
lemma of_le_refl_apply {I : discrete_quotient X} (i : I) :
of_le (le_refl _) i = i := by tidy

end discrete_quotient
