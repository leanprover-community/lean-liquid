import category_theory.category.ulift
import category_theory.limits.filtered_colimit_commutes_finite_limit -- todo: minimize imports
import data.real.nnreal

noncomputable theory
open_locale nnreal

open category_theory

namespace category_theory.limits

variables (ι : ℕ →o ℝ≥0) (hι : ∀ r : ℝ≥0, ∃ n : ℕ, r ≤ ι n)

def find_nat (r : ℝ≥0) : ℕ := (hι r).some

lemma find_nat_spec (r : ℝ≥0) : r ≤ ι (find_nat ι hι r) :=
(hι r).some_spec

def nat_to_nnreal : ℕ ⥤ ℝ≥0 :=
{ obj := λ i, ι i,
  map := λ i j h, hom_of_le $ ι.mono h.le }

universes v u
variables {C : Type u} [category.{v} C]

def restrict_diagram (F : as_small.{v} ℝ≥0 ⥤ C) :
  as_small.{v} ℕ ⥤ C :=
(as_small.down ⋙ nat_to_nnreal ι ⋙ as_small.up) ⋙ F

def restrict_cocone {F : as_small.{v} ℝ≥0 ⥤ C} (S : cocone F) :
  cocone (restrict_diagram ι F) :=
S.whisker _

def is_colimit_restrict_cocone {F : as_small.{v} ℝ≥0 ⥤ C} (S : cocone F) (hS : is_colimit S) :
  is_colimit (restrict_cocone ι S) :=
{ desc := λ T, hS.desc ⟨T.X,
  { app := λ r, F.map (as_small.up.map $ hom_of_le $ find_nat_spec ι hι (ulift.down r)) ≫
        T.ι.app (ulift.up (find_nat ι hι (ulift.down r))),
    naturality' := begin
      intros r s f,
      dsimp,
      let m := find_nat ι hι (ulift.down r) ⊔ find_nat ι hι (ulift.down s),
      let r' := as_small.up.obj (find_nat ι hι (ulift.down r)),
      let s' := as_small.up.obj (find_nat ι hι (ulift.down s)),
      let m' := as_small.up.obj m,
      let ιr : r' ⟶ m' := as_small.up.map (hom_of_le $ le_sup_left),
      let ιs : s' ⟶ m' := as_small.up.map (hom_of_le $ le_sup_right),
      erw ← T.w ιr,
      erw ← T.w ιs,
      dsimp [restrict_diagram],
      simp only [category.comp_id, ← category.assoc, ← F.map_comp],
      refl,
    end }⟩,
  fac' := begin
    intros W j,
    dsimp [restrict_cocone],
    rw hS.fac,
    dsimp,
    let r := (nat_to_nnreal ι).obj (ulift.down j),
    let k := find_nat ι hι r,
    let l := (ulift.down j) ⊔ k,
    let k' : as_small.{v} ℕ := as_small.up.obj k,
    let l' : as_small.{v} ℕ := as_small.up.obj l,
    let ιk : k' ⟶ l' := as_small.up.map (hom_of_le $ le_sup_right),
    let ιj : j ⟶ l' := as_small.up.map (hom_of_le $ le_sup_left),
    erw ← W.w ιk,
    erw ← W.w ιj,
    dsimp [restrict_diagram],
    simp only [← category.assoc, ← F.map_comp],
    refl,
  end,
  uniq' := begin
    intros W m hm,
    apply hS.hom_ext, intros j,
    specialize hm (as_small.up.obj (find_nat ι hι (ulift.down j))),
    dsimp [restrict_cocone] at hm,
    rw hS.fac,
    dsimp,
    erw [← hm, ← category.assoc, S.w],
  end }

end category_theory.limits
