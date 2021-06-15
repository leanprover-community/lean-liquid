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

lemma is_closed_bUnion' {ι X : Type*} [topological_space X] :
  Π (F : finset ι) (Vs : Π (i : ι) (hi : i ∈ F), set X)
  (hVs : ∀ (i : ι) (hi : i ∈ F), is_closed (Vs i hi)),
  is_closed (⋃ (i : ι) (hi : i ∈ F), Vs i hi) :=
begin
  intros F,
  apply F.induction_on,
  { intros Vs hVs,
    simp },
  { intros i F hi hF Vs h2,
    have hh1 : ∀ (a : ι) (ha : a ∈ F), a ∈ insert i F := by finish,
    have hh2 : i ∈ insert i F := by finish,
    have : (⋃ (a : ι) (ha : a ∈ insert i F), Vs a ha) =
      (Vs i hh2) ∪ (⋃ (a : ι) (ha : a ∈ F), Vs a (hh1 _ ha)),
    { ext x,
      split,
      { intro h,
        rcases h with ⟨a,⟨a,rfl⟩,ha⟩,
        dsimp at ha,
        rcases ha with ⟨ha,⟨ha,rfl⟩,hhh⟩,
        rw finset.mem_insert at ha,
        cases ha with ha1 ha1,
        { left,
          subst ha1,
          exact hhh },
        { right,
          refine ⟨Vs a ha, ⟨a, _⟩, hhh⟩,
          simp [ha1] } },
      { intro h,
        cases h with h h,
        { refine ⟨_, ⟨i, _⟩, h⟩,
          simp },
        { rcases h with ⟨_,⟨a,rfl⟩,hh⟩,
          rcases hh with ⟨hh1,⟨hh2,rfl⟩,hh3⟩,
          refine ⟨_,⟨a,_⟩,hh3⟩,
          simp [hh2] } } },
    rw this,
    apply is_closed.union,
    apply h2,
    apply hF,
    intros a ha,
    apply h2 }
end
