import topology.discrete_quotient

namespace discrete_quotient

variables {X : Type*} [topological_space X] (S : discrete_quotient X)

section comap

variables {Y : Type*} [topological_space Y] {f : Y → X} (cont : continuous f)

@[simp]
lemma comap_id : S.comap (continuous_id : continuous (id : X → X)) = S := by {ext, refl}

@[simp]
lemma comap_comp {Z : Type*} [topological_space Z] {g : Z → Y} (cont' : continuous g) :
  S.comap (continuous.comp cont cont') = (S.comap cont).comap cont' := by {ext, refl}

lemma comap_mono {A B : discrete_quotient X} (h : A ≤ B) : A.comap cont ≤ B.comap cont :=
by tauto

end comap

section of_le

@[simp]
lemma of_le_refl {A : discrete_quotient X} : of_le (le_refl A) = id := by {ext ⟨⟩, refl}

lemma of_le_refl_apply {A : discrete_quotient X} (a : A) : of_le (le_refl A) a = a := by simp

@[simp]
lemma of_le_comp {A B C : discrete_quotient X} (h1 : A ≤ B) (h2 : B ≤ C) :
  of_le (le_trans h1 h2) = of_le h2 ∘ of_le h1 := by {ext ⟨⟩, refl}

lemma of_le_comp_apply {A B C : discrete_quotient X} (h1 : A ≤ B) (h2 : B ≤ C) (a : A) :
  of_le (le_trans h1 h2) a = of_le h2 (of_le h1 a) := by simp

end of_le

section map

variables {Y : Type*} [topological_space Y] {f : Y → X}
  (cont : continuous f) (A : discrete_quotient Y) (B : discrete_quotient X)

/--
Given `cont : continuous f`, `le_rel cont A B` is defined as `A ≤ B.comap f`.
Mathematically this means that `f` descends to a morphism `A → B`.
-/
def le_rel : Prop := A ≤ B.comap cont

variables {cont A B}

lemma le_rel_id (A : discrete_quotient X) : le_rel continuous_id A A := by tauto

lemma le_rel_comp {Z : Type*} [topological_space Z] {g : Z → Y} {cont' : continuous g}
  {C : discrete_quotient Z} : le_rel cont' C A → le_rel cont A B →
  le_rel (continuous.comp cont cont') C B := by tauto

lemma le_rel_trans {C : discrete_quotient X} :
  le_rel cont A B → B ≤ C → le_rel cont A C := λ h1 h2, le_trans h1 $ comap_mono _ h2

/-- Map a discrete quotient along a continuous map. -/
def map (cond : le_rel cont A B) : A → B := quotient.map' f cond

lemma map_continuous (cond : le_rel cont A B) : continuous (map cond) :=
continuous_of_discrete_topology

@[simp]
lemma map_proj (cond : le_rel cont A B) : map cond ∘ A.proj = B.proj ∘ f := rfl

@[simp]
lemma map_proj_apply (cond : le_rel cont A B) (y : Y) : map cond (A.proj y) = B.proj (f y) := rfl

@[simp]
lemma map_id : map (le_rel_id A) = id := by {ext ⟨⟩, refl}

@[simp]
lemma map_comp {Z : Type*} [topological_space Z] {g : Z → Y} {cont' : continuous g}
  {C : discrete_quotient Z} (h1 : le_rel cont' C A) (h2 : le_rel cont A B) :
  map (le_rel_comp h1 h2) = map h2 ∘ map h1 := by {ext ⟨⟩, refl}

@[simp]
lemma of_le_map {C : discrete_quotient X} (cond : le_rel cont A B) (h : B ≤ C) :
   map (le_rel_trans cond h) = of_le h ∘ map cond := by {ext ⟨⟩, refl}

@[simp]
lemma of_le_map_apply {C : discrete_quotient X} (cond : le_rel cont A B) (h : B ≤ C) (a : A) :
  map (le_rel_trans cond h) a = of_le h (map cond a) := by {rcases a, refl}

@[simp]
lemma map_of_le {C : discrete_quotient Y} (cond : le_rel cont A B) (h : C ≤ A) :
   map (le_trans h cond) = map cond ∘ of_le h := by {ext ⟨⟩, refl}

@[simp]
lemma map_of_le_apply {C : discrete_quotient Y} (cond : le_rel cont A B) (h : C ≤ A) (c : C) :
  map (le_trans h cond) c = map cond (of_le h c) := by {rcases c, refl}

end map

end discrete_quotient
