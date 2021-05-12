import category_theory.preadditive
import algebraic_topology.cech_nerve
import for_mathlib.simplicial.complex
import for_mathlib.simplicial.augmented
import for_mathlib.arrow.split
import for_mathlib.fin

namespace category_theory

universes v u

namespace arrow

noncomputable theory
open_locale simplicial
open category_theory.limits

variables {C : Type u} [category.{v} C] (f : arrow C) [split f]
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- The splittings of the Cech nerve associated to a split arrow. -/
def cech_splitting (n : ℕ) : f.cech_nerve _[n] ⟶ f.cech_nerve _[n+1] :=
wide_pullback.lift (wide_pullback.base _)
(λ i, if h : i.down = 0 then wide_pullback.base _ ≫ split.σ else wide_pullback.π _ ⟨i.down.pred h⟩)
begin
  rintro ⟨j⟩,
  split_ifs,
  tidy,
end

@[simp]
lemma face_zero_π (n : ℕ) (i : fin (n+1)) :
  (f.cech_nerve.δ 0 : f.cech_nerve _[n+1] ⟶ _) ≫ wide_pullback.π _ ⟨i⟩ =
  wide_pullback.π _ ⟨i.succ⟩ :=
begin
  change wide_pullback.lift _ _ _ ≫ _ = _,
  simpa,
end

@[simp]
lemma cech_splitting_face_zero (n : ℕ) :
  f.cech_splitting n ≫ f.cech_nerve.δ 0 = 𝟙 _ :=
begin
  ext ⟨j⟩,
  dsimp [cech_splitting, simplicial_object.δ],
  simp only [category.id_comp, category.assoc, wide_pullback.lift_π],
  split_ifs,
  { exfalso,
    exact fin.succ_ne_zero _ h },
  { congr,
    dsimp [simplicial_object.δ, simplex_category.δ],
    simp },
  { dsimp [simplicial_object.δ, cech_splitting],
    simp },
end

@[simp]
lemma face_π (n : ℕ) (i : fin (n+1)) (j : fin (n+2)) :
  (f.cech_nerve.δ j : f.cech_nerve _[n+1] ⟶ _) ≫ wide_pullback.π _ ⟨i⟩ =
  wide_pullback.π _ ⟨j.succ_above i⟩ :=
begin
  change wide_pullback.lift _ _ _ ≫ _ = _,
  simpa,
end

@[simp]
lemma cech_splitting_face (n : ℕ) (j : fin (n+3)) (hj : j ≠ 0) :
  f.cech_splitting (n+1) ≫ f.cech_nerve.δ j =
  f.cech_nerve.δ (j.pred hj) ≫ f.cech_splitting n :=
begin
  ext ⟨k⟩,
  swap,
  { dsimp [cech_splitting, simplicial_object.δ],
    simp },
  { dsimp [cech_splitting, simplicial_object.δ],
    simp only [category.assoc, limits.wide_pullback.lift_π],
    split_ifs with h1 h2,
    { simp },
    { refine false.elim (h2 _),
      change j.succ_above k = 0 at h1,
      change k = 0,
      rwa ← fin.succ_above_eq_zero_iff _ _ hj },
    { refine false.elim (h1 _),
      erw h,
      change j.succ_above 0 = 0,
      rw fin.succ_above_eq_zero_iff _ _ hj },
    { simp only [category_theory.limits.wide_pullback.lift_π],
      congr,
      change (j.succ_above k).pred h1 = (j.pred hj).succ_above (k.pred h),
      change j.succ_above k ≠ 0 at h1,
      change k ≠ 0 at h,
      rw fin.succ_above_pred } }
end

end arrow

namespace arrow

section contracting_homotopy

open category_theory.limits opposite

-- Note: Universe restrictions! I hope this doesn't pose any issues later...
variables {P N : Type u} [category.{v} P] [category.{v} N] [preadditive N] (M : Pᵒᵖ ⥤ N)
variables (f : arrow P) [arrow.split f]
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

@[simps]
def conerve : cosimplicial_object.augmented N :=
{ left := M.obj (op f.right),
  right := f.cech_nerve.right_op ⋙ M,
  hom :=
  { app := λ m, M.map (f.augmented_cech_nerve.hom.app (op m)).op,
    naturality' := begin
      -- opposites are annoying.
      intros m n f,
      dsimp,
      simp only [← M.map_comp, ← M.map_id],
      congr' 1,
      simp only [← op_comp, ← op_id],
      congr' 1,
      simp,
    end } }

def contracting_homotopy : Π (n : ℕ),
  (f.conerve M).to_cocomplex.X (n+1) ⟶ (f.conerve M).to_cocomplex.X n
| 0 := M.map $ quiver.hom.op $
         wide_pullback.lift
           (𝟙 f.right)
           (λ i : ulift (fin (0+1)), (split.σ : f.right ⟶ f.left))
           (by simp)
| (n+1) := M.map (f.cech_splitting n).op

#check f.contracting_homotopy M 0

lemma is_contracting_homotopy_zero :
  (f.conerve M).to_cocomplex.d 0 1 ≫ f.contracting_homotopy M 0 = 𝟙 _ :=
begin
  dsimp,
  split_ifs,
  swap, finish,
  dsimp [contracting_homotopy,
    cosimplicial_object.augmented.to_cocomplex_d,
    cosimplicial_object.augmented.to_cocomplex_obj],
  simp only [category.comp_id, ← M.map_comp, ← M.map_id, ← op_id, ← op_comp],
  congr' 2,
  simp,
end

lemma is_contracting_homotopy_one :
  (f.conerve M).to_cocomplex.d 1 2 ≫ f.contracting_homotopy M 1 +
  f.contracting_homotopy M 0 ≫ (f.conerve M).to_cocomplex.d 0 1 = 𝟙 _ :=
begin
  dsimp,
  rw if_pos,
  swap, refl,
  dsimp [contracting_homotopy,
    cosimplicial_object.augmented.to_cocomplex_d,
    cosimplicial_object.coboundary],
  simp [fin.sum_univ_succ],
  simp_rw ← M.map_comp,
  rw ← add_zero (𝟙 ((conerve M f).to_cocomplex_obj 1)),
  rw add_assoc,
  congr' 1,
  { dsimp [conerve, cosimplicial_object.augmented.to_cocomplex_obj],
    rw ← M.map_id,
    congr' 1,
    simp_rw [← op_comp, ← op_id],
    congr' 1,
    dsimp [cech_splitting],
    sorry,
    --tidy
  },
  { rw neg_add_eq_zero,
    congr' 1,
    simp_rw ← op_comp,
    congr' 1,
    dsimp [cech_splitting],
    tidy,
  }
end

lemma is_contracting_homotopy (n : ℕ) :
  (f.conerve M).to_cocomplex.d (n+2) (n+3) ≫ f.contracting_homotopy M (n+2) +
  f.contracting_homotopy M (n+1) ≫ (f.conerve M).to_cocomplex.d (n+1) (n+2) = 𝟙 _ :=
begin
  sorry
end

end contracting_homotopy

end arrow

end category_theory
