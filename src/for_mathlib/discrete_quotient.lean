import topology.discrete_quotient

namespace discrete_quotient

variables {X Y : Type*} [topological_space X] [topological_space Y]

lemma le_comap_of_eq {f : X → Y} {cont : continuous f} (S : discrete_quotient X)
  (T : discrete_quotient Y) (h : S.rel = (T.comap cont).rel) : le_comap cont S T :=
begin
  have : S = T.comap cont, by {ext1, assumption},
  rw this,
  tauto,
end

lemma map_injective {f : X → Y} (cont : continuous f) (S : discrete_quotient X)
  (T : discrete_quotient Y) (h : S.rel = (T.comap cont).rel) :
  function.injective (map (le_comap_of_eq S T h)) :=
begin
  intros a b hh,
  obtain ⟨a,rfl⟩ := S.proj_surjective a,
  obtain ⟨b,rfl⟩ := S.proj_surjective b,
  replace hh : T.proj _ = T.proj _ := hh,
  apply quotient.sound',
  change S.rel _ _,
  rw h,
  dsimp [comap],
  replace hh := @quotient.exact' _ T.setoid _ _ hh,
  exact hh,
end

instance [h : nonempty X] (S : discrete_quotient X) : nonempty S :=
begin
  obtain x := nonempty.some h,
  use S.proj x,
end

end discrete_quotient

open_locale classical
noncomputable theory

variables {X Y : Type*}

-- Ugh
def choose_section [hnn : nonempty X] (f : X → Y) : Y → X :=
λ y, if hh : ∃ x : X, f x = y then classical.some hh else nonempty.some hnn

lemma choose_section_is_section (f : X → Y) (inj : function.injective f)
  (a : X) : @choose_section X Y ⟨a⟩ f (f a) = a :=
begin
  dsimp [choose_section],
  split_ifs,
  { have := classical.some_spec h,
    exact inj this },
  { exfalso,
    apply h,
    use a }
end
