import topology.constructions

open topological_space

lemma pi_induced_induced {ι : Sort*} {X Y : ι → Type*} [t : Π i : ι, topological_space $ Y i]
 (f : Π i, X i → Y i) : @Pi.topological_space ι X (λ i, induced (f i) (t i)) =
  induced (λ (x : Π i, X i), (λ j,  f j (x j) : Π i, Y i)) Pi.topological_space :=
begin
  dsimp [Pi.topological_space],
  rw induced_infi,
  simp [induced_compose]
end
