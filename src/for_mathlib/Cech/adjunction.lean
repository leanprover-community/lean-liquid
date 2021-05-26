import algebraic_topology.cech_nerve

universe u

noncomputable theory

open_locale simplicial

namespace simplex_category

/-- The constant morphism from [0]. -/
def const (x : simplex_category.{u}) (i : fin (x.len+1)) : [0] ⟶ x :=
  hom.mk $ ⟨λ _, i, by tauto⟩

@[simp]
lemma const_comp (x y : simplex_category.{u}) (i : fin (x.len + 1)) (f : x ⟶ y) :
  const x i ≫ f = const y (f.to_preorder_hom i) := rfl

end simplex_category

namespace category_theory

open category_theory.limits

variables {C : Type*} [category C]

namespace simplicial_object.augmented

/-- The functor from augmented objects to arrows. -/
@[simps]
def to_arrow : simplicial_object.augmented C ⥤ arrow C :=
{ obj := λ X,
  { left := (drop.obj X) _[0],
    right := (point.obj X),
    hom := X.hom.app _ },
  map := λ X Y η,
  { left := (drop.map η).app _,
    right := (point.map η),
    w' := begin
      dsimp,
      rw ← nat_trans.comp_app,
      erw η.w,
      refl,
    end } }

end simplicial_object.augmented

namespace simplicial_object

variables [∀ (n : ℕ) (f : arrow C),
  has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- A helper function used in defining the Cech adjunction. -/
@[simps]
def equivalence_right_to_left (X : simplicial_object.augmented C) (F : arrow C)
  (G : X ⟶ F.augmented_cech_nerve) : (augmented.to_arrow.obj X ⟶ F) :=
{ left := G.left.app _ ≫ wide_pullback.π _ ⟨0⟩,
  right := G.right,
  w' := begin
    have := G.w,
    apply_fun (λ e, e.app (opposite.op $ simplex_category.mk 0)) at this,
    tidy,
  end }

/-- A helper function used in defining the Cech adjunction. -/
@[simps]
def equivalence_left_to_right (X : simplicial_object.augmented C) (F : arrow C)
  (G : augmented.to_arrow.obj X ⟶ F) : (X ⟶ F.augmented_cech_nerve) :=
{ left :=
  { app := λ x, limits.wide_pullback.lift (X.hom.app _ ≫ G.right)
      (λ i, X.left.map (simplex_category.const x.unop i.down).op ≫ G.left) (by tidy),
    naturality' := begin
      intros x y f,
      ext,
      { dsimp,
        simp only [wide_pullback.lift_π, category.assoc],
        rw [← category.assoc, ← X.left.map_comp],
        refl },
      { dsimp,
        simp only [functor.const.obj_map, nat_trans.naturality_assoc,
          wide_pullback.lift_base, category.assoc],
        erw category.id_comp }
    end },
  right := G.right }

/-- A helper function used in defining the Cech adjunction. -/
@[simps]
def cech_nerve_equiv (X : simplicial_object.augmented C) (F : arrow C) :
  (augmented.to_arrow.obj X ⟶ F) ≃ (X ⟶ F.augmented_cech_nerve) :=
{ to_fun := equivalence_left_to_right _ _,
  inv_fun := equivalence_right_to_left _ _,
  left_inv := begin
    intro A,
    dsimp,
    ext,
    { dsimp,
      erw wide_pullback.lift_π,
      nth_rewrite 1 ← category.id_comp A.left,
      congr' 1,
      convert X.left.map_id _,
      rw ← op_id,
      congr' 1,
      ext ⟨a,ha⟩,
      change a < 1 at ha,
      change 0 = a,
      linarith },
    { refl, }
  end,
  right_inv := begin
    intro A,
    dsimp,
    ext _ ⟨j⟩,
    { dsimp,
      simp only [arrow.cech_nerve_map, wide_pullback.lift_π, nat_trans.naturality_assoc],
      erw wide_pullback.lift_π,
      refl },
    { dsimp,
      erw wide_pullback.lift_base,
      have := A.w,
      apply_fun (λ e, e.app x) at this,
      rw nat_trans.comp_app at this,
      erw this,
      refl },
    { refl }
  end }

/-- The augmented Cech nerve construction is right adjoint to the `to_arrow` functor. -/
@[simps]
def cech_adjunction : (augmented.to_arrow : _ ⥤ arrow C) ⊣
  simplicial_object.augmented_cech_nerve :=
adjunction.mk_of_hom_equiv { hom_equiv := cech_nerve_equiv }

end simplicial_object

end category_theory
