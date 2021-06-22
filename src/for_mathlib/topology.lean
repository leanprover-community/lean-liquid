import topology.order
import topology.bases
import data.finset.basic

open_locale classical

open topological_space

lemma is_closed.sdiff {X : Type*} [topological_space X] {S T : set X} :
  is_closed S → is_open T → is_closed (S \ T) :=
begin
  intros h1 h2,
  rw (show S \ T = S ∩ Tᶜ, by refl),
  apply is_closed.inter h1,
  simpa using h2,
end
