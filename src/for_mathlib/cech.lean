import category_theory.limits.shapes.terminal
import category_theory.over
import category_theory.limits.cones
import algebraic_topology.simplicial_object
import .fan

noncomputable theory

namespace simplicial_object

local attribute [tidy] tactic.case_bash

open category_theory

universes v u

variables {C : Type u} [category.{v} C] {X B : C} (f : X ⟶ B)

abbreviation ufin (n : ℕ) := ulift.{v} (fin n)
abbreviation ufin.map {m n : ℕ} (h : fin m → fin n) : ufin m → ufin n :=
  λ i, ulift.up (h i.down)
abbreviation ufin.mk {n} (x : fin n) : ufin n := ulift.up x

abbreviation Cech.diagram (a : simplex_category.{v}) : fan (ufin.{v} (a.len+1)) ⥤ C :=
fan.mk (λ i, X) (λ i, f)

abbreviation Cech.map_cone {a b : simplex_category.{v}ᵒᵖ} (h : a ⟶ b)
  (CC : limits.cone (Cech.diagram f a.unop)) : limits.cone (Cech.diagram f b.unop) :=
fan.map_cone (ufin.map h.unop.to_preorder_hom) _ _ CC

abbreviation Cech.obj_aux [∀ x : simplex_category.{v}, limits.has_limit (Cech.diagram f x)]
  (a : simplex_category.{v}ᵒᵖ) : C := limits.limit (Cech.diagram f a.unop)

abbreviation Cech.map_aux [∀ x : simplex_category.{v}, limits.has_limit (Cech.diagram f x)]
{a b : simplex_category.{v}ᵒᵖ} (h : a ⟶ b) : Cech.obj_aux f a ⟶ Cech.obj_aux f b :=
limits.limit.lift (Cech.diagram f b.unop) (Cech.map_cone _ h _)

@[simps]
def Cech_aux [∀ x : simplex_category.{v}, limits.has_limit (Cech.diagram f x)] :
  simplicial_object C :=
{ obj := λ a, Cech.obj_aux f a,
  map := λ a b g, Cech.map_aux f g,
  map_comp' := begin
    intros x y z f g,
    delta Cech.map_aux Cech.map_cone Cech.diagram,
    ext ⟨j|j⟩,
    { delta fan.map_cone, tidy },
    { delta fan.map_cone, tidy }
  end }.

open_locale simplicial

@[derive category, simp]
protected def over (B : C) :=
over ((category_theory.functor.const simplex_category.{v}ᵒᵖ).obj B)

namespace over

@[simp]
def forget : simplicial_object.over B ⥤ simplicial_object C := over.forget _

@[simps]
def to_hom : simplicial_object.over B ⥤ category_theory.over B :=
{ obj := λ X, over.mk (X.hom.app (opposite.op [0])),
  map := λ X Y f, over.hom_mk (f.left.app _) }

end over

@[simp]
def Cech_to_const [∀ x : simplex_category.{v}, limits.has_limit (Cech.diagram f x)] :
  Cech_aux f ⟶ (category_theory.functor.const simplex_category.{v}ᵒᵖ).obj B :=
{ app := λ x, limits.limit.π _ fan.right }

@[simp]
def Cech [∀ x : simplex_category.{v}, limits.has_limit (Cech.diagram f x)] :
  simplicial_object.over B := over.mk (Cech_to_const f)

@[simps]
def hom_to_cone (f : over B) : limits.cone (Cech.diagram f.hom [0]) :=
{ X := f.left,
  π := { app := λ x,
    match x with
    | fan.right := f.hom
    | fan.left _ := 𝟙 _
    end,
  naturality' := begin
    intros x y f,
    cases x; cases y; cases f,
    erw [category.id_comp, category.comp_id],
    any_goals {erw [category.id_comp]},
  end } }

@[simps]
def Cech_to_hom (f : over B)
  [∀ (x : simplex_category.{v}), limits.has_limit (Cech.diagram f.hom x)] :
  over.to_hom.obj (Cech f.hom) ≅ f :=
{ hom :=
  { left := limits.limit.π _ (fan.left (begin
      apply ufin.mk,
      exact (0 : fin (0+1)), -- :-(
    end )),
    right := { down := { down := by simp } },
    w' := begin
      dsimp,
      rw [category.comp_id],
      convert limits.limit.w (Cech.diagram f.hom [0]) (fan.hom.of (_)),
    end },
  inv :=
  { left := limits.limit.lift _ (hom_to_cone _),
    right := ⟨⟨by simp⟩⟩ },
  hom_inv_id' := begin
    -- TODO: clean up this proof.
    dsimp [hom_to_cone],
    ext ⟨j|j⟩,
    { tidy,
      unfold hom_to_cone,
      have := limits.limit.w (Cech.diagram f.hom [0]) (fan.hom.of (ufin.mk 0)),
      erw ← this,
      congr' 1 },
    { tidy,
      unfold hom_to_cone,
      have := limits.limit.w (Cech.diagram f.hom [0]) (fan.hom.of (ufin.mk 0)),
      erw [category.comp_id] }
  end }.

-- TODO: move this
def point_incl (x : simplex_category) (i : fin (x.len + 1)) : [0] ⟶ x :=
begin
  -- TODO: Use terms, not a tactic block!
  have : x = [x.len], by simp, rw this,
  apply simplex_category.mk_hom,
  refine ⟨λ h, i, _⟩,
  tidy,
end

-- TODO: move this
def point_proj (x : simplex_categoryᵒᵖ) (i : fin (x.unop.len + 1)) : x ⟶ (opposite.op [0]) :=
begin
  -- TODO: Use terms, not a tactic block!
  have : x = (opposite.op x.unop), by simp, rw this,
  exact (point_incl _ i).op
end

@[simps]
def equiv_cone (x : simplex_category.{v}ᵒᵖ) (f : over B) (Y : simplicial_object.over B)
  (F : over.to_hom.obj Y ⟶ f) :
  limits.cone (Cech.diagram f.hom x.unop) :=
{ X := Y.left.obj x,
  π :=
  { app := λ i,
    match i with
    | fan.right := Y.hom.app x
    | fan.left j := Y.left.map (point_proj x j.down) ≫ F.left
    end,
    naturality' := begin
      intros x y f,
      cases x; cases y; cases f,
      { erw [category.id_comp, category.comp_id] },
      { dsimp,
        erw [category.id_comp],
        dsimp [fan.mk],
        have this := F.w,
        dsimp at this,
        rw [category.comp_id] at this,
        erw [category.assoc, this],
        tidy },
      { erw [category.id_comp, category.comp_id] },
    end } }.

def Cech.equiv
  [∀ (f : over B) (x : simplex_category.{v}), limits.has_limit (Cech.diagram f.hom x)]
  (f : over B) (Y : simplicial_object.over B) :
  (over.to_hom.obj Y ⟶ f) ≃ (Y ⟶ Cech f.hom) :=
{ to_fun := λ F,
  { left :=
    { app := λ x, limits.limit.lift (Cech.diagram f.hom x.unop) (equiv_cone x f Y F),
      naturality' := sorry },
    right := { down := { down := by simp } },
    w' := sorry },
  inv_fun := λ F, over.to_hom.map F ≫ (Cech_to_hom f).hom,
  left_inv := sorry,
  right_inv := sorry }

end simplicial_object
