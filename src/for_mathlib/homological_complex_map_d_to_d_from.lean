import algebra.homology.homological_complex
import algebra.homology.additive

noncomputable theory

universes v

open category_theory category_theory.limits

variables {C D : Type*} [category C] [category D]
variables [has_zero_object C] [has_zero_object D]
variables {M : Type*} {c : complex_shape M}

namespace category_theory

namespace functor

variables [preadditive C] [preadditive D]
variables (F : C ⥤ D) [functor.additive F] (X Y : homological_complex C c)

def obj_X_prev (i : M) : F.obj (X.X_prev i) ≅ ((F.map_homological_complex c).obj X).X_prev i :=
iso.refl _

lemma obj_X_prev_hom_eq (j i : M) (hij : c.rel j i) :
  (F.obj_X_prev X i).hom = 𝟙 _ := rfl

lemma map_prev_iso_hom (j i : M) (hij : c.rel j i) :
  F.map (X.X_prev_iso hij).hom = (((F.map_homological_complex c).obj X).X_prev_iso hij).hom :=
by { obtain rfl := c.prev_eq' hij, exact F.map_id _ }

def obj_X_next {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i : M) :
  F.obj (X.X_next i) ≅ ((F.map_homological_complex c).obj X).X_next i :=
iso.refl _

lemma obj_X_next_hom_eq (i j : M) (hij : c.rel i j) :
  (F.obj_X_next X i).hom = 𝟙 _ := rfl

lemma map_next_iso_inv (i j : M) (hij : c.rel i j) :
  F.map (X.X_next_iso hij).inv = (((F.map_homological_complex c).obj X).X_next_iso hij).inv :=
by { obtain rfl := c.next_eq' hij, exact F.map_id _ }

lemma map_d_to (i : M) :
  F.map (X.d_to i) = ((F.map_homological_complex c).obj X).d_to i := rfl

lemma d_from_map (i : M) :
  F.map (X.d_from i) = ((F.map_homological_complex c).obj X).d_from i := rfl

variables {X Y}

def map_prev (f : X ⟶ Y) (i : M) :
  F.map (homological_complex.hom.prev f i) =
    homological_complex.hom.prev ((F.map_homological_complex c).map f) i := rfl

def map_next (f : X ⟶ Y) (i : M) :
  F.map (homological_complex.hom.next f i) =
    homological_complex.hom.next ((F.map_homological_complex c).map f) i := rfl

end functor

namespace nat_trans

variables [preadditive C] [preadditive D]
  {F G : C ⥤ D} [functor.additive F] [functor.additive G] (φ : F ⟶ G)
  (X : homological_complex C c)

lemma map_prev (i : M) : φ.app (X.X_prev i) =
    homological_complex.hom.prev ((nat_trans.map_homological_complex φ c).app X) i := rfl

lemma map_next (i : M) : φ.app (X.X_next i) =
    homological_complex.hom.next ((nat_trans.map_homological_complex φ c).app X) i := rfl

end nat_trans

end category_theory
