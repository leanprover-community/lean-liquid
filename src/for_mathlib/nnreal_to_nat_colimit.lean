import category_theory.category.ulift
import category_theory.limits.filtered_colimit_commutes_finite_limit -- todo: minimize imports
import data.real.nnreal

noncomputable theory
open_locale nnreal

open category_theory

namespace category_theory.limits

variables (c : ℝ≥0) [fact (0 < c)]

lemma exists_int_mul (r : ℝ≥0) : ∃ n : ℕ, r ≤ ↑n * c :=
begin
  refine ⟨nat.ceil (r / c), _⟩,
  transitivity r / c * c,
  { rw div_mul_cancel,
    exact ne_of_gt (fact.out _) },
  { exact (mul_le_mul_right (fact.out _)).mpr (nat.le_ceil _) },
end

def find_int_mul (r : ℝ≥0) : ℕ := (exists_int_mul c r).some

lemma find_int_mul_spec (r : ℝ≥0) : r ≤ ↑(find_int_mul c r) * c :=
(exists_int_mul c r).some_spec

def nat_to_nnreal : ℕ ⥤ ℝ≥0 :=
{ obj := λ i, ↑i * c,
  map := λ i j h, hom_of_le $
    mul_le_mul (by exact_mod_cast h.le) (le_refl _) (zero_le _) (zero_le _) }

universes v u
variables {C : Type u} [category.{v} C]

def restrict_diagram (F : as_small.{v} ℝ≥0 ⥤ C) :
  as_small.{v} ℕ ⥤ C :=
(as_small.down ⋙ nat_to_nnreal c ⋙ as_small.up) ⋙ F

def restrict_cocone {F : as_small.{v} ℝ≥0 ⥤ C} (S : cocone F) :
  cocone (restrict_diagram c F) :=
S.whisker _

def is_colimit_restrict_cocone {F : as_small.{v} ℝ≥0 ⥤ C} (S : cocone F) (hS : is_colimit S) :
  is_colimit (restrict_cocone c S) :=
{ desc := λ T, hS.desc ⟨T.X,
  { app := λ r, F.map (as_small.up.map $ hom_of_le $ find_int_mul_spec c (ulift.down r)) ≫
        T.ι.app (ulift.up (find_int_mul c (ulift.down r))),
    naturality' := begin
      intros r s f,
      dsimp,
      let m := find_int_mul c (ulift.down r) ⊔ find_int_mul c (ulift.down s),
      let r' := as_small.up.obj (find_int_mul c (ulift.down r)),
      let s' := as_small.up.obj (find_int_mul c (ulift.down s)),
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
    let r := (nat_to_nnreal c).obj (ulift.down j),
    let k := find_int_mul c r,
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
    specialize hm (as_small.up.obj (find_int_mul c (ulift.down j))),
    dsimp [restrict_cocone] at hm,
    rw hS.fac,
    dsimp,
    erw [← hm, ← category.assoc, S.w],
  end }

end category_theory.limits
