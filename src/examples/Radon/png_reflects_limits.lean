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
  (h : ∀ j, continuous (C.π.app j ∘ t)) : continuous t := sorry

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

def lift : S.X ⟶ C.X :=
{ to_fun := lift_fun _ hC _,
  map_zero' := by sorry ; begin
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
  end,
  map_add' := begin
    sorry
    -- similar to map_zero' above.
  end,
  strict' := by sorry ; begin
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
  continuous' := by sorry ; begin
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
  fac' := sorry,
  uniq' := sorry }

end CompHausFiltPseuNormGrp₁
