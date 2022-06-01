import category_theory.preadditive
import algebraic_topology.cech_nerve

import for_mathlib.simplicial.complex
import for_mathlib.arrow.split

namespace category_theory

universes v u v' u'

namespace arrow

noncomputable theory
open_locale simplicial
open category_theory.limits

variables {C : Type u} [category.{v} C] (f : arrow C)
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- The splittings of the Cech nerve associated to a split arrow. -/
def cech_splitting [split f] (n : ℕ) : f.cech_nerve _[n] ⟶ f.cech_nerve _[n+1] :=
wide_pullback.lift (wide_pullback.base _)
(λ i, if h : i.down = 0 then wide_pullback.base _ ≫ split.σ else wide_pullback.π _ ⟨i.down.pred h⟩)
begin
  rintro ⟨j⟩,
  split_ifs,
  tidy,
end

lemma cech_splitting_face_zero [split f] (n : ℕ) :
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

lemma face_π (n : ℕ) (i : fin (n+1)) (j : fin (n+2)) :
  (f.cech_nerve.δ j : f.cech_nerve _[n+1] ⟶ _) ≫ wide_pullback.π _ ⟨i⟩ =
  wide_pullback.π _ ⟨j.succ_above i⟩ :=
begin
  change wide_pullback.lift _ _ _ ≫ _ = _,
  simpa,
end

lemma cech_splitting_face [split f] (n : ℕ) (j : fin (n+3)) (hj : j ≠ 0) :
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
      rwa ← fin.succ_above_eq_zero_iff hj },
    { refine false.elim (h1 _),
      erw h,
      change j.succ_above 0 = 0,
      rw fin.succ_above_eq_zero_iff hj },
    { simp only [category_theory.limits.wide_pullback.lift_π],
      congr,
      change (j.succ_above k).pred h1 = (j.pred hj).succ_above (k.pred h),
      rw fin.pred_succ_above_pred,
      refl } }
end

end arrow

namespace arrow

section contracting_homotopy

open category_theory.limits opposite

-- Note: Universe restrictions! I hope this doesn't pose any issues later...
-- jmc: seems like it might! I removed them.
variables {P : Type u} {N : Type u'} [category.{v} P] [category.{v'} N] (M : Pᵒᵖ ⥤ N)
variables (f : arrow P)
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- The augmented Cech conerve induced by applying M to `f.augmented_cech_nerve`. -/
abbreviation conerve : cosimplicial_object.augmented N :=
((cosimplicial_object.augmented.whiskering _ _).obj M).obj f.augmented_cech_nerve.right_op

variables [arrow.split f] [preadditive N]

/-- The morphisms yielding the contracting homotopy. -/
def contracting_homotopy : Π (n : ℕ),
  (f.conerve M).to_cocomplex.X (n+1) ⟶ (f.conerve M).to_cocomplex.X n
| 0 := M.map (wide_pullback.lift (𝟙 _)
         (λ i, (split.σ : f.right ⟶ _))
         (by simp)).op
| (n+1) := M.map (f.cech_splitting n).op

open cosimplicial_object.augmented
open_locale big_operators

lemma is_contracting_homotopy_zero :
  (f.conerve M).to_cocomplex.d 0 1 ≫ f.contracting_homotopy M 0 = 𝟙 _ :=
begin
  dsimp,
  rw if_pos,
  swap, { simp },
  delta conerve,
  dsimp [to_cocomplex_d, to_cocomplex_obj, contracting_homotopy ],
  simp only [category.id_comp, category.comp_id],
  simp_rw [← M.map_comp, ← op_comp, ← M.map_id, ← op_id],
  congr' 2,
  simp,
end

lemma is_contracting_homotopy_one :
  (f.conerve M).to_cocomplex.d 1 2 ≫ f.contracting_homotopy M 1 +
  f.contracting_homotopy M 0 ≫ (f.conerve M).to_cocomplex.d 0 1 = 𝟙 _ :=
begin
  rw ← add_zero (𝟙 ((conerve M f).to_cocomplex.X 1)),
  dsimp only [to_cocomplex, cochain_complex.of],
  rw dif_pos,
  swap, { dec_trivial },
  rw dif_pos,
  swap, { dec_trivial },
  dsimp,
  delta conerve,
  dsimp only [to_cocomplex_d, cosimplicial_object.coboundary, whiskering, whiskering_obj,
    drop, to_cocomplex_obj, comma.snd, cosimplicial_object.whiskering, whiskering_right,
    contracting_homotopy],
  simp_rw fin.sum_univ_succ,
  simp only [fin.coe_zero, fin.sum_univ_zero, fin.coe_one,
    one_zsmul, preadditive.add_comp, pow_one, fin.succ_zero_eq_one,
    category.id_comp, neg_smul, category.comp_id, preadditive.neg_comp, pow_zero ],
  rw [add_assoc],
  congr' 1,
  { dsimp [cosimplicial_object.δ],
    simp_rw [← M.map_comp, ← M.map_id, ← op_id, ← op_comp],
    congr' 2,
    dsimp [cech_splitting],
    ext ⟨j⟩,
    { simp only [wide_pullback.lift_π, category.id_comp, category.assoc],
      split_ifs,
      { cases j,
        dsimp at h,
        injection h with hh,
        simp only [nat.succ_ne_zero] at hh,
        cases hh },
      { congr, } },
    { simp only [wide_pullback.lift_base, category.assoc, category.id_comp] } },
  { dsimp [cosimplicial_object.δ],
    rw [add_assoc, neg_add_eq_zero, ← M.map_comp],
    simp only [zero_comp, category.id_comp, zero_add, functor.map_comp, ← M.map_comp, ← op_comp],
    congr' 2,
    dsimp [cech_splitting],
    ext ⟨j⟩,
    { simp only [wide_pullback.lift_π, category.assoc],
      split_ifs,
      { refl },
      { refine false.elim (h _),
        change (1 : fin 2).succ_above j = 0,
        rw fin.succ_above_eq_zero_iff,
        { simp },
        { exact top_ne_bot } } },
    { simp only [wide_pullback.lift_base, category.assoc, category.comp_id] } }
end

lemma is_contracting_homotopy (n : ℕ) :
  (f.conerve M).to_cocomplex.d (n+2) (n+3) ≫ f.contracting_homotopy M (n+2) +
  f.contracting_homotopy M (n+1) ≫ (f.conerve M).to_cocomplex.d (n+1) (n+2) = 𝟙 _ :=
begin
  dsimp,
  erw if_pos,
  swap, refl,
  dsimp only [to_cocomplex_d],
  rw if_pos,
  swap, refl,
  dsimp only [cosimplicial_object.coboundary],
  simp only [preadditive.sum_comp, preadditive.comp_sum],
  erw [fin.sum_univ_succ, add_assoc, ← finset.sum_add_distrib],
  rw ← add_zero (𝟙 ((conerve M f).to_cocomplex_obj (n + 2))),
  dsimp only [cosimplicial_object.δ],
  congr' 1,
  { delta conerve,
    dsimp [to_cocomplex_obj, contracting_homotopy],
    simp only [category_theory.category.comp_id, one_zsmul, pow_zero],
    simp_rw [← M.map_id, ← M.map_comp, ← op_comp, ← op_id],
    congr' 2,
    apply cech_splitting_face_zero },
  { apply fintype.sum_eq_zero,
    intros i,
    simp only [
      category.comp_id,
      add_zero,
      functor.comp_map,
      fin.coe_succ,
      preadditive.comp_zsmul,
      preadditive.zsmul_comp],
    suffices :
      (drop.obj (conerve M f)).map (simplex_category.δ i.succ) ≫ contracting_homotopy M f (n+2) =
          contracting_homotopy M f (n+1) ≫ (drop.obj (conerve M f)).map (simplex_category.δ i),
    { rw [this, pow_succ],
      simp },
    delta conerve,
    dsimp [contracting_homotopy],
    simp_rw [← M.map_comp, ← op_comp],
    congr' 2,
    convert cech_splitting_face _ _ _ (fin.succ_ne_zero _),
    funext,
    congr,
    simp }
end

end contracting_homotopy

section covariant_contracting_homotopy

open category_theory.limits opposite

variables {P : Type u} {N : Type u'} [category.{v} P] [category.{v'} N] (M : P ⥤ N)
variables (f : arrow P)
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- The augmented Cech nerve induced by applying M to `f.augmented_cech_nerve`. -/
abbreviation nerve : simplicial_object.augmented N :=
((simplicial_object.augmented.whiskering _ _).obj M).obj f.augmented_cech_nerve

variables [arrow.split f] [preadditive N]

open simplicial_object.augmented
open_locale big_operators

def covariant_contracting_homotopy : Π (n : ℕ),
  (f.nerve M).to_complex.X n ⟶ (f.nerve M).to_complex.X (n+1)
| 0 := M.map $ wide_pullback.lift (𝟙 _) (λ i, (split.σ : f.right ⟶ _)) (by simpa)
| (n+1) := M.map $ f.cech_splitting n

lemma covariant_is_contracting_homotopy_zero :
  f.covariant_contracting_homotopy M 0 ≫ (f.nerve M).to_complex.d 1 0 = 𝟙 _ :=
begin
  dsimp,
  rw if_pos,
  swap, { simp },
  delta nerve,
  dsimp [to_complex_obj, to_complex_d, covariant_contracting_homotopy],
  simp only [category.id_comp, category.comp_id],
  simp_rw [← M.map_comp, ← M.map_id],
  congr' 2,
  simp,
end

lemma covariant_is_contracting_homotopy_one :
  f.covariant_contracting_homotopy M 1 ≫ (f.nerve M).to_complex.d 2 1 +
  (f.nerve M).to_complex.d 1 0 ≫ f.covariant_contracting_homotopy M 0 = 𝟙 _ :=
begin
  dsimp [covariant_contracting_homotopy],
  rw if_pos, rw if_pos, any_goals { dec_trivial },
  dsimp [to_complex_d, simplicial_object.boundary, simplicial_object.δ],
  delta nerve,
  dsimp [to_complex_obj],
  simp only [fin.sum_univ_succ, fin.coe_zero, pow_zero, one_zsmul, fintype.univ_of_subsingleton,
    nat.add_def, fin.mk_eq_subtype_mk, fin.mk_zero, fin.coe_succ, pow_one, neg_smul,
    finset.sum_singleton, preadditive.comp_add, category.id_comp,
    preadditive.comp_neg, category.comp_id],
  simp only [← M.map_comp],
  rw add_assoc,
  convert add_zero _,
  swap,
  { symmetry,
    convert M.map_id _,
    dsimp [arrow.cech_splitting],
    ext ⟨⟨j,hj⟩⟩, simp,
    rw dif_neg, refl,
    dsimp [simplex_category.δ],
    have : j = 0, by simpa using hj, subst this, dec_trivial,
    simp },
  { rw neg_add_eq_zero,
    congr' 1,
    dsimp [cech_splitting],
    ext ⟨⟨j,hj⟩⟩,
    { simp only [category.assoc, wide_pullback.lift_π], dsimp,
      rw dif_pos, have : j = 0, by simpa using hj, subst this,
      dsimp [simplex_category.δ], dec_trivial },
    { simp } }
end

lemma covariant_is_contracting_homotopy (n : ℕ) :
  f.covariant_contracting_homotopy M (n+2) ≫ (f.nerve M).to_complex.d (n+3) (n+2) +
  (f.nerve M).to_complex.d (n+2) (n+1) ≫ f.covariant_contracting_homotopy M (n+1) = 𝟙 _ :=
begin
  dsimp, rw if_pos, rw if_pos, swap, { refl }, swap, { refl },
  simp only [category.comp_id, category.id_comp],
  dsimp only [to_complex_d, simplicial_object.boundary],
  simp only [preadditive.sum_comp, preadditive.comp_sum],
  rw [fin.sum_univ_succ, add_assoc, ← finset.sum_add_distrib],
  convert add_zero _,
  { apply fintype.sum_eq_zero, intros j,
    have : ((j.succ : fin _) : ℕ) = (j : ℕ) + 1 := by simp, rw this, clear this,
    rw [pow_succ],
    simp only [neg_mul, one_mul, neg_smul, preadditive.comp_neg],
    rw neg_add_eq_zero,
    simp only [preadditive.comp_zsmul, preadditive.zsmul_comp],
    congr' 1,
    dsimp [covariant_contracting_homotopy, simplicial_object.δ],
    delta nerve,
    dsimp [whiskering],
    simp only [← M.map_comp],
    congr' 1,
    convert cech_splitting_face _ _ _ (fin.succ_ne_zero _), funext i,
    congr, simp },
  { dsimp [covariant_contracting_homotopy],
    simp only [pow_zero, one_zsmul],
    delta nerve,
    dsimp [arrow.cech_splitting, simplicial_object.whiskering, simplicial_object.δ],
    rw ← M.map_comp, symmetry,
    convert M.map_id _,
    ext ⟨⟨j,hj⟩⟩,
    simp only [category.assoc, wide_pullback.lift_π],
    rw dif_neg, dsimp, simpa, dsimp [simplex_category.δ],
    intro c, apply_fun (λ e, e.1) at c, simpa using c,
    simp, dsimp, simp }
end

end covariant_contracting_homotopy

end arrow

end category_theory
