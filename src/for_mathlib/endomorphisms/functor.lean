import for_mathlib.endomorphisms.basic

noncomputable theory

universes v u

open category_theory category_theory.limits

namespace category_theory

variables {C D : Type*} [category C] [category D]

namespace functor

@[simps]
def map_endomorphisms (F : C ⥤ D) : endomorphisms C ⥤ endomorphisms D :=
{ obj := λ X, ⟨F.obj X.X, F.map X.e⟩,
  map := λ X Y f, ⟨F.map f.f, by { rw [← F.map_comp, ← F.map_comp, f.comm] }⟩,
  map_id' := λ X, by { ext, exact F.map_id _ },
  map_comp' := λ X Y Z f g, by { ext, exact F.map_comp _ _ } }

end functor

@[simps]
def nat_trans.map_endomorphisms {F G : C ⥤ D} (η : F ⟶ G) :
  F.map_endomorphisms ⟶ G.map_endomorphisms :=
{ app := λ T, ⟨η.app _, by tidy⟩ }

end category_theory
