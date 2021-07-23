import topology.discrete_quotient

namespace discrete_quotient

variables (X : Type*) [topological_space X] [discrete_topology X]

instance : order_bot (discrete_quotient X) :=
{ bot :=
  { rel := λ a b , a = b,
    equiv := ⟨λ a, rfl, λ a b h, h.symm, λ a b c h1 h2, h1.trans h2⟩,
    clopen := λ x, ⟨is_open_discrete _, is_closed_discrete _⟩ },
  bot_le := by { rintro S a b (h : a = b), rw h, exact S.refl _ },
  ..(infer_instance : semilattice_inf _) }

lemma proj_bot_injective : function.injective (⊥ : discrete_quotient X).proj :=
λ a b h, quotient.exact' h

lemma proj_bot_bijective : function.bijective (⊥ : discrete_quotient X).proj :=
⟨proj_bot_injective _, proj_surjective _⟩

end discrete_quotient
