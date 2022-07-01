import algebra.homology.homological_complex
import algebra.homology.additive

noncomputable theory

universes v

open category_theory category_theory.limits

variables {C D : Type*} [category C] [category D]
variables [has_zero_object C] [has_zero_object D]
variables {M : Type*} {c : complex_shape M}

/- there are already `prev_eq_zero` and `next_eq_zero`
  in `les_homology.lean`, but with extra assumptions -/
lemma homological_complex.prev_eq_zero' [has_zero_morphisms C]
  {X Y : homological_complex C c} (f : X ⟶ Y) (i : M) (h : c.prev i = none) : f.prev i = 0 :=
by { dsimp [homological_complex.hom.prev], simpa only [h], }

lemma homological_complex.next_eq_zero' [has_zero_morphisms C]
  {X Y : homological_complex C c} (f : X ⟶ Y) (i : M) (h : c.next i = none) : f.next i = 0 :=
by { dsimp [homological_complex.hom.next], simpa only [h], }

namespace category_theory

namespace functor

variables [preadditive C] [preadditive D]
variables (F : C ⥤ D) [functor.additive F] (X Y : homological_complex C c)

def obj_X_prev (i : M) : F.obj (X.X_prev i) ≅ ((F.map_homological_complex c).obj X).X_prev i :=
begin
  rcases h : c.prev i with _ | ⟨j, hij⟩,
  { exact F.map_iso (homological_complex.X_prev_iso_zero X h) ≪≫ (map_zero_object F) ≪≫
      (homological_complex.X_prev_iso_zero _ h).symm, },
  { exact F.map_iso (homological_complex.X_prev_iso X hij) ≪≫ (by refl) ≪≫
    (homological_complex.X_prev_iso _ hij).symm, },
end

lemma obj_X_prev_hom_eq (j i : M) (hij : c.rel j i) :
  (F.obj_X_prev X i).hom = F.map (homological_complex.X_prev_iso X hij).hom ≫
    (eq_to_hom (by refl)) ≫ (homological_complex.X_prev_iso _ hij).inv :=
begin
  dsimp [homological_complex.X_prev_iso, obj_X_prev],
  simp only [c.prev_eq_some hij, eq_to_iso_map, iso.refl_trans, iso.trans_hom,
    eq_to_iso.hom, iso.symm_hom, eq_to_iso.inv, eq_to_hom_map, category.id_comp],
end

@[reassoc]
lemma map_prev_iso_hom (j i : M) (hij : c.rel j i) :
  F.map (X.X_prev_iso hij).hom = (F.obj_X_prev X i).hom ≫
    (((F.map_homological_complex c).obj X).X_prev_iso hij).hom :=
by simp only [F.obj_X_prev_hom_eq X j i hij, eq_to_hom_refl,
    category.assoc, iso.inv_hom_id, category.comp_id]

def obj_X_next {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i : M) :
  F.obj (X.X_next i) ≅ ((F.map_homological_complex c).obj X).X_next i :=
begin
  rcases h : c.next i with _ | ⟨j, hij⟩,
  { exact F.map_iso (homological_complex.X_next_iso_zero X h) ≪≫ (map_zero_object F) ≪≫
      (homological_complex.X_next_iso_zero _ h).symm, },
  { exact F.map_iso (homological_complex.X_next_iso X hij) ≪≫ (by refl) ≪≫
    (homological_complex.X_next_iso _ hij).symm, },
end

lemma obj_X_next_hom_eq (i j : M) (hij : c.rel i j) :
  (F.obj_X_next X i).hom = F.map (homological_complex.X_next_iso X hij).hom ≫
    (eq_to_hom (by refl)) ≫ (homological_complex.X_next_iso _ hij).inv :=
begin
  dsimp [homological_complex.X_next_iso, obj_X_next],
  simp only [c.next_eq_some hij, eq_to_iso_map, iso.refl_trans, iso.trans_hom,
    eq_to_iso.hom, iso.symm_hom, eq_to_iso.inv, eq_to_hom_map, category.id_comp],
end

@[reassoc]
lemma map_next_iso_inv (i j : M) (hij : c.rel i j) :
  F.map (X.X_next_iso hij).inv ≫ (F.obj_X_next X i).hom =
    (((F.map_homological_complex c).obj X).X_next_iso hij).inv :=
by simp only [F.obj_X_next_hom_eq X i j hij, ← F.map_comp_assoc,
    eq_to_hom_refl, category.id_comp, iso.inv_hom_id, map_id]

lemma map_d_to (i : M) :
  F.map (X.d_to i) = (F.obj_X_prev X i).hom ≫ ((F.map_homological_complex c).obj X).d_to i :=
begin
  rcases h : c.prev i with _ | ⟨j, hij⟩,
  { simp only [homological_complex.d_to_eq_zero _ h, functor.map_zero, comp_zero], },
  { rw homological_complex.d_to_eq _ hij,
    rw homological_complex.d_to_eq _ hij,
    rw ← ((F.map_homological_complex c).obj X).X_prev_iso_comp_d_to hij,
    simp only [map_comp, homological_complex.X_prev_iso_comp_d_to, map_homological_complex_obj_d,
      map_prev_iso_hom_assoc], },
end

lemma d_from_map (i : M) :
  F.map (X.d_from i) ≫ (F.obj_X_next X i).hom = ((F.map_homological_complex c).obj X).d_from i :=
begin
  rcases h : c.next i with _ | ⟨j, hij⟩,
  { simp only [homological_complex.d_from_eq_zero _ h, functor.map_zero, zero_comp], },
  { rw homological_complex.d_from_eq _ hij,
    rw homological_complex.d_from_eq _ hij,
    rw ← ((F.map_homological_complex c).obj X).d_from_comp_X_next_iso hij,
    simp only [map_comp, category.assoc, homological_complex.d_from_comp_X_next_iso,
      map_homological_complex_obj_d, map_next_iso_inv], },
end

variables {X Y}

def map_prev (f : X ⟶ Y) (i : M) :
  F.map (homological_complex.hom.prev f i) ≫ (F.obj_X_prev Y i).hom =
  (F.obj_X_prev X i).hom ≫ homological_complex.hom.prev ((F.map_homological_complex c).map f) i :=
begin
  rcases h : c.prev i with _ | ⟨j, hij⟩,
  { simp only [homological_complex.prev_eq_zero' _ _ h, functor.map_zero,
      zero_comp, comp_zero], },
  { simp only [homological_complex.hom.prev_eq _ hij,
      F.obj_X_prev_hom_eq _ j i hij,
      F.map_comp, eq_to_hom_refl, category.id_comp],
    slice_lhs 3 4 { rw [← F.map_comp, iso.inv_hom_id, F.map_id], },
    simp only [category.id_comp, map_homological_complex_map_f, category.assoc,
      iso.inv_hom_id_assoc], },
end

def map_next (f : X ⟶ Y) (i : M) :
  F.map (homological_complex.hom.next f i) ≫ (F.obj_X_next Y i).hom =
  (F.obj_X_next X i).hom ≫ homological_complex.hom.next ((F.map_homological_complex c).map f) i :=
begin
  rcases h : c.next i with _ | ⟨j, hij⟩,
  { simp only [homological_complex.next_eq_zero' _ _ h, functor.map_zero,
      zero_comp, comp_zero], },
  { simp only [homological_complex.hom.next_eq _ hij,
      F.obj_X_next_hom_eq _ i j hij, F.map_comp, eq_to_hom_refl, category.id_comp],
    slice_lhs 3 4 { rw [← F.map_comp, iso.inv_hom_id, F.map_id], },
    simp only [category.id_comp, map_homological_complex_map_f, category.assoc,
      iso.inv_hom_id_assoc], },
end

end functor

namespace nat_trans

variables [preadditive C] [preadditive D]
  {F G : C ⥤ D} [functor.additive F] [functor.additive G] (φ : F ⟶ G)
  (X : homological_complex C c)

lemma map_prev (i : M) : φ.app (X.X_prev i) ≫ (G.obj_X_prev X i).hom =
  (F.obj_X_prev X i).hom ≫
    homological_complex.hom.prev ((nat_trans.map_homological_complex φ c).app X) i :=
begin
  rcases h : c.prev i with _ | ⟨j, hij⟩,
  { suffices : φ.app (X.X_prev i) = 0,
    { simp only [this, homological_complex.prev_eq_zero' _ _ h, zero_comp, comp_zero], },
    apply is_zero.eq_zero_of_src,
    exact is_zero.of_iso (is_zero_zero _)
      (F.map_iso (X.X_prev_iso_zero h) ≪≫ F.map_zero_object), },
  { simp only [functor.obj_X_prev_hom_eq _ X j i hij,
      eq_to_hom_refl, category.id_comp, category.assoc, ← φ.naturality_assoc,
      homological_complex.hom.prev_eq _ hij, iso.inv_hom_id_assoc,
      map_homological_complex_app_f], },
end

lemma map_next (i : M) : φ.app (X.X_next i) ≫ (G.obj_X_next X i).hom =
  (F.obj_X_next X i).hom ≫
    homological_complex.hom.next ((nat_trans.map_homological_complex φ c).app X) i :=
begin
  rcases h : c.next i with _ | ⟨j, hij⟩,
  { suffices : φ.app (X.X_next i) = 0,
    { simp only [this, homological_complex.next_eq_zero' _ _ h, zero_comp, comp_zero], },
    apply is_zero.eq_zero_of_tgt,
    exact is_zero.of_iso (is_zero_zero _)
      (G.map_iso (X.X_next_iso_zero h) ≪≫ G.map_zero_object), },
  { simp only [functor.obj_X_next_hom_eq _ X i j hij,
      eq_to_hom_refl, category.id_comp, category.assoc, ← φ.naturality_assoc,
      homological_complex.hom.next_eq _ hij, iso.inv_hom_id_assoc,
      map_homological_complex_app_f], },
end

end nat_trans

end category_theory
