import pseudo_normed_group.bounded_limits
import category_theory.limits.concrete_category

open category_theory
open category_theory.limits
open_locale nnreal

universes u
variables {J : Type u} [small_category J]
  {F : J ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (C : cone F)

namespace CompHaus

lemma comp_apply {X Y Z : CompHaus} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := rfl

lemma continuous_of_is_limit (F : J ⥤ CompHaus.{u}) (C : cone F) (hC : is_limit C)
  (Y : Type u) [topological_space Y] (t : Y → C.X)
  (h : ∀ j, continuous (C.π.app j ∘ t)) : continuous t :=
begin
  let CC := CompHaus_to_Top.map_cone C,
  let hCC : is_limit CC := is_limit_of_preserves CompHaus_to_Top hC,
  let E : cone (F ⋙ CompHaus_to_Top) := ⟨Top.of Y, λ j, ⟨_,h j⟩, _⟩,
  convert (hCC.lift E).continuous,
  ext1 a,
  apply concrete.is_limit_ext _ hCC, intros j,
  change _ = (hCC.lift E ≫ CC.π.app j) _,
  rw hCC.fac, refl,
  intros i j f, ext, dsimp,
  change _ = (C.π.app _ ≫ F.map _) _,
  rw C.w,
end

end CompHaus

namespace CompHausFiltPseuNormGrp₁

noncomputable theory

def lvl (X : CompHausFiltPseuNormGrp₁) (x : X) : ℝ≥0 :=
(X.exhaustive x).some

lemma lvl_spec (X : CompHausFiltPseuNormGrp₁) (x : X) :
  x ∈ pseudo_normed_group.filtration X (X.lvl x) :=
(X.exhaustive x).some_spec

def as_lvl (X : CompHausFiltPseuNormGrp₁) (x : X) :
  (level.obj (X.lvl x)).obj X :=
⟨x, (X.lvl_spec x)⟩

@[reassoc]
lemma level_cone_compatible (c₁ c₂ : ℝ≥0) (e : c₁ ⟶ c₂) (j) :
  (level.map e).app _ ≫ ((level.obj _).map_cone C).π.app j =
  ((level.obj _).map_cone C).π.app j ≫ (level.map e).app _ := rfl

namespace level_jointly_reflects_limits

variables (hC : Π c : ℝ≥0, is_limit ((level.obj c).map_cone C))
variables (S : cone F)

def lift_fun : S.X → C.X :=
λ s, ((hC (S.X.lvl s)).lift ((level.obj _).map_cone S) (S.X.as_lvl s)).1

lemma lift_fun_map_zero : lift_fun C hC S 0 = 0 :=
begin
  dsimp [lift_fun],
  let a := ((hC (S.X.lvl 0)).lift ((level.obj (S.X.lvl 0)).map_cone S)) (S.X.as_lvl 0),
  let b := (C.X.as_lvl 0),
  let c₁ := S.X.lvl 0,
  let c₂ := C.X.lvl 0,
  let c := c₁ ⊔ c₂,
  let i1 : c₁ ⟶ c := hom_of_le le_sup_left,
  let i2 : c₂ ⟶ c := hom_of_le le_sup_right,
  let e1 := (level.map i1).app C.X,
  let e2 := (level.map i2).app C.X,
  change (e1 a).1 = (e2 b).1, congr' 1,
  apply concrete.is_limit_ext _ (hC c),
  intros j, dsimp only [e1, e2, a, b, ← CompHaus.comp_apply],
  simp only [category.assoc, level_cone_compatible, (hC (S.X.lvl 0)).fac_assoc],
  ext1,
  dsimp [CompHaus.comp_apply, level, as_lvl],
  rw [(S.π.app j).map_zero, (C.π.app j).map_zero],
end

lemma fac_aux (c) (x) (j) :
  C.π.app j ((hC c).lift ((level.obj c).map_cone S) x).1 =
  S.π.app j x.1 :=
begin
  change
    (((hC c).lift ((level.obj c).map_cone S) ≫
      (level.obj c).map (C.π.app j)) x).1 = _,
  erw (hC c).fac,
  refl,
end

lemma lift_fun_map_add (x y) : lift_fun C hC S (x + y) =
  lift_fun C hC S x + lift_fun C hC S y :=
begin
  dsimp [lift_fun],
  let Axy := ((hC (S.X.lvl (x + y))).lift
    ((level.obj (S.X.lvl (x + y))).map_cone S)) (S.X.as_lvl (x + y)),
  let Ax := ((hC (S.X.lvl x)).lift
    ((level.obj (S.X.lvl x)).map_cone S)) (S.X.as_lvl x),
  let Ay := ((hC (S.X.lvl y)).lift
    ((level.obj (S.X.lvl y)).map_cone S)) (S.X.as_lvl y),
  let cxy := S.X.lvl (x + y),
  let cx := S.X.lvl x,
  let cy := S.X.lvl y,
  let cc := cxy ⊔ (cx + cy),
  let AA : (level.obj (cx + cy)).obj C.X :=
    ⟨Ax.1 + Ay.1, pseudo_normed_group.add_mem_filtration Ax.2 Ay.2⟩,
  let i1 : cxy ⟶ cc := hom_of_le le_sup_left,
  let i2 : (cx + cy) ⟶ cc := hom_of_le le_sup_right,
  let e1 := (level.map i1).app C.X,
  let e2 := (level.map i2).app C.X,
  change (e1 Axy).1 = (e2 AA).1, congr' 1,
  apply concrete.is_limit_ext _ (hC cc), intros j,
  dsimp only [e1, e2, Axy, ← CompHaus.comp_apply],
  simp only [category.assoc, level_cone_compatible,
    (hC (S.X.lvl (x + y))).fac_assoc],
  ext1,
  dsimp [CompHaus.comp_apply, level, as_lvl, AA],

  rw [(S.π.app j).map_add, (C.π.app j).map_add],
  congr' 1,
  { dsimp only [Ax],
    erw fac_aux, refl },
  { dsimp only [Ay],
    erw fac_aux, refl },
end

def lift : S.X ⟶ C.X :=
{ to_fun := lift_fun _ hC _,
  map_zero' := lift_fun_map_zero _ _ _,
  map_add' := lift_fun_map_add _ _ _,
  strict' := begin
    intros c x hx,
    let y : (level.obj c).obj S.X := ⟨x,hx⟩,
    let z := (hC c).lift ((level.obj c).map_cone S) y,
    let a := ((hC (S.X.lvl x)).lift ((level.obj (S.X.lvl x)).map_cone S)) (S.X.as_lvl x),
    suffices : a.1 = z.1,
    { dsimp only [lift_fun], rw this, exact z.2, },
    let cc := c ⊔ S.X.lvl x,
    let i1 : c ⟶ cc := hom_of_le le_sup_left,
    let i2 : S.X.lvl x ⟶ cc := hom_of_le le_sup_right,
    suffices : (level.map i1).app _ z = (level.map i2).app _ a,
    { apply_fun (λ e, e.1) at this, exact this.symm },
    dsimp [a,z],
    apply concrete.is_limit_ext _ (hC cc),
    intros j,
    simp only [← CompHaus.comp_apply, category.assoc, level_cone_compatible,
      (hC c).fac_assoc, (hC (S.X.lvl x)).fac_assoc],
    ext, refl,
  end,
  continuous' := begin
    intros c,
    let t : _ → (level.obj c).obj C.X := _, change continuous t,
    suffices : ∀ j, continuous (((level.obj c).map (C.π.app j)) ∘ t),
    { exact CompHaus.continuous_of_is_limit (F ⋙ level.obj c)
        ((level.obj c).map_cone C) (hC c) _ _ this },
    intros j,
    convert ((level.obj c).map (S.π.app j)).continuous,
    ext1 a,
    let cc : ℝ≥0 := c ⊔ (S.X.lvl a),
    let i1 : c ⟶ cc := hom_of_le le_sup_left,
    let i2 : (S.X.lvl a) ⟶ cc := hom_of_le le_sup_right,
    apply_fun ((level.map i1).app _), swap,
    { intros x y h, ext1, apply_fun (λ e, e.1) at h, exact h },
    simp only [← CompHaus.comp_apply],
    simp only [nat_trans.naturality],
    dsimp [t],
    generalize_proofs hh,
    let q := ((level.map i1).app C.X) (pseudo_normed_group.level (lift_fun C hC S) hh c a),
    have : q = ((level.map i2).app C.X)
      (((hC (S.X.lvl a)).lift ((level.obj (S.X.lvl a)).map_cone S)) (S.X.as_lvl a)), refl,
    dsimp only [q] at this,
    simp only [this, ← CompHaus.comp_apply, category.assoc],
    erw level_cone_compatible,
    rw (hC (S.X.lvl a)).fac_assoc,
    ext, refl,
  end }

end level_jointly_reflects_limits

def level_jointly_reflects_limits
  (hC : Π c : ℝ≥0, is_limit ((level.obj c).map_cone C)) :
  is_limit C :=
{ lift := λ S, level_jointly_reflects_limits.lift _ hC _,
  fac' := begin
    intros S j,
    ext1 t,
    dsimp [level_jointly_reflects_limits.lift,
      level_jointly_reflects_limits.lift_fun],
    erw level_jointly_reflects_limits.fac_aux, refl,
  end,
  uniq' := begin
    intros S m hm,
    ext1 t,
    dsimp [level_jointly_reflects_limits.lift,
      level_jointly_reflects_limits.lift_fun],
    let a :=
      ((hC (S.X.lvl t)).lift ((level.obj (S.X.lvl t)).map_cone S)) (S.X.as_lvl t),
    let c := C.X.lvl (m t),
    let d := c ⊔ (S.X.lvl t),
    let i1 : c ⟶ d := hom_of_le le_sup_left,
    let i2 : (S.X.lvl t) ⟶ d := hom_of_le le_sup_right,
    change ((level.map i1).app C.X (C.X.as_lvl (m t))).1 =
      ((level.map i2).app C.X a).1,
    congr' 1,
    apply concrete.is_limit_ext _ (hC d), intros j,
    specialize hm j,
    ext1,
    dsimp [level, as_lvl, a],
    erw level_jointly_reflects_limits.fac_aux,
    rw ← hm, refl,
  end }

def create_hom_from_level {X Y : CompHausFiltPseuNormGrp₁}
  (E : Π c, (level.obj c).obj X ⟶ (level.obj c).obj Y)
  (hE0 : (E (X.lvl 0) (X.as_lvl 0)).1 = 0)
  (hEa : ∀ a b : X, (E _ (X.as_lvl (a + b))).1 =
    (E _ (X.as_lvl a)).1 + (E _ (X.as_lvl b)).1)
  (hE : ∀ (c₁ c₂ : ℝ≥0) (i : c₁ ⟶ c₂),
    E _ ≫ (level.map i).app _ = (level.map i).app _ ≫ E _) :
  X ⟶ Y :=
{ to_fun := λ x, (E _ $ X.as_lvl x).1,
  map_zero' := hE0,
  map_add' := hEa,
  strict' := begin
    intros c x hx,
    let y : (level.obj c).obj X := ⟨x,hx⟩,
    suffices : ((E (X.lvl x)) (X.as_lvl x)).val = (E _ y).1,
    { rw this, exact (E _ y).2, },
    let d := c ⊔ X.lvl x,
    let i1 : c ⟶ d := hom_of_le le_sup_left,
    let i2 : X.lvl x ⟶ d := hom_of_le le_sup_right,
    change ((level.map i2).app Y ((E (X.lvl x)) (X.as_lvl x))).1 =
      ((level.map i1).app _ _).1,
    congr' 1,
    simp only [← CompHaus.comp_apply, hE],
    refl,
  end,
  continuous' := begin
    intros c,
    let t := _, change continuous t,
    convert (E c).continuous,
    ext a,
    let d := X.lvl a ⊔ c,
    let i1 : X.lvl a ⟶ d := hom_of_le le_sup_left,
    let i2 : c ⟶ d := hom_of_le le_sup_right,
    change ((level.map i1).app _ (E _ (X.as_lvl a))).1 =
      ((level.map i2).app _ (E _ a)).1,
    simp only [← CompHaus.comp_apply, hE], refl,
  end }

def create_iso_from_level {X Y : CompHausFiltPseuNormGrp₁}
  (E : Π c, (level.obj c).obj X ≅ (level.obj c).obj Y)
  (hE0 : ((E (X.lvl 0)).hom (X.as_lvl 0)).1 = 0)
  (hEa : ∀ a b : X, ((E _).hom (X.as_lvl (a + b))).1 =
    ((E _).hom (X.as_lvl a)).1 + ((E _).hom (X.as_lvl b)).1)
  (hE : ∀ (c₁ c₂ : ℝ≥0) (i : c₁ ⟶ c₂),
    (E _).hom ≫ (level.map i).app _ = (level.map i).app _ ≫ (E _).hom) :
  X ≅ Y :=
{ hom := create_hom_from_level (λ c, (E c).hom) hE0 hEa hE,
  inv := create_hom_from_level (λ c, (E c).inv)
    sorry sorry sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

end CompHausFiltPseuNormGrp₁
