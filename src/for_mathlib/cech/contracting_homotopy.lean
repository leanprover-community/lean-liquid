import .split
import for_mathlib.simplicial.complex

open_locale big_operators

noncomputable theory

namespace category_theory

namespace cech

-- TODO: make sure the universe levels work for the necessary applications

universes u

variables {P : Type (u+1)} {C : Type (u+1)} [large_category P] [large_category C] [preadditive C]
variables {X B : P} (f : X ⟶ B) [∀ (n : ℕ), limits.has_wide_pullback B (λ (i : ufin (n+1)), X) (λ i, f)]
variables (M : Pᵒᵖ ⥤ C)
variables (g : B ⟶ X) (splitting : g ≫ f = 𝟙 B)

abbreviation conerve : cosimplicial_object C := (cech_obj f).right_op ⋙ M

abbreviation conerve_complex : cochain_complex ℕ C := cosimplicial_object.cocomplex.obj $ conerve f M

abbreviation contracting_homotopy (n : ℕ) :
  (conerve_complex f M).X (n+1) ⟶ (conerve_complex f M).X n :=
M.map $ (cech_splitting f g splitting n).op

section finset_sum_helpers

lemma helper.sum_eq {n} {α : Type*} [add_comm_monoid α] (ι : fin (n+1) → α) :
  (∑ (i : fin (n+1)), ι i) = ι 0 + ∑ i : fin n, ι i.succ :=
fin.sum_univ_succ (λ (i : fin (n + 1)), ι i)

lemma helper.sum_eq_zero_of_zeros {n} {α : Type*} [add_comm_monoid α] (ι : fin n → α) :
  (∀ i, ι i = 0) → ∑ i, ι i = 0 := λ h, fintype.sum_eq_zero (λ (a : fin n), ι a) h

lemma helper.op_comp {E : Type*} [category E] {a b c : E} (h : a ⟶ b) (l : b ⟶ c) :
  (h ≫ l).op = l.op ≫ h.op := rfl

lemma helper.op_id {E : Type*} [category E] {a : E} :
  (𝟙 a).op = 𝟙 (opposite.op a) := rfl

lemma helper.op_eq_id {E : Type*} [category E] {a : E} (h : a ⟶ a) :
  h.op = 𝟙 _ ↔ h = 𝟙 _ :=
begin
  split,
  { intro h, apply quiver.hom.op_inj, exact h },
  { intro h, rw h, refl }
end

end finset_sum_helpers

theorem is_contracting_homotopy (n : ℕ) :
  (conerve_complex f M).d (n+1) (n+2) ≫ contracting_homotopy f M g splitting (n+1) +
  contracting_homotopy f M g splitting n ≫ (conerve_complex f M).d n (n+1) = 𝟙 _ :=
begin
  delta conerve_complex,
  dsimp only [cosimplicial_object.cocomplex, cosimplicial_object.to_cocomplex, cochain_complex.mk'],
  split_ifs,
  swap, finish,
  swap, finish,
  swap, finish,
  dsimp only [cosimplicial_object.coboundary],
  simp only [preadditive.sum_comp, preadditive.comp_sum],
  rw [helper.sum_eq, add_assoc, ← finset.sum_add_distrib],
  rw ← add_zero (𝟙 _),
  swap, apply_instance,
  congr' 1,
  { simp only [category_theory.category.comp_id,
    fin.coe_zero,
    one_gsmul,
    category_theory.eq_to_hom_refl,
    category_theory.functor.comp_map,
    --category_theory.cech_obj_map,
    category_theory.functor.right_op_map,
    pow_zero],
    delta contracting_homotopy,
    rw ← M.map_comp,
    erw ← M.map_id,
    congr' 1,
    rw ← helper.op_comp,
    erw helper.op_eq_id,
    erw cech_splitting_face_zero },
  { apply helper.sum_eq_zero_of_zeros,
    intros i,
    simp only [category_theory.category.comp_id,
      category_theory.preadditive.comp_gsmul,
      category_theory.preadditive.gsmul_comp,
      category_theory.eq_to_hom_refl,
      category_theory.functor.comp_map,
      --category_theory.cech_obj_map,
      fin.coe_succ,
      category_theory.functor.right_op_map],
    delta contracting_homotopy,
    simp_rw ← M.map_comp,
    suffices :
      ((cech_obj f).map (simplex_category.δ i.succ).op).op ≫ (cech_splitting f g splitting (n + 1)).op =
      (cech_splitting f g splitting n).op ≫ ((cech_obj f).map (simplex_category.δ i).op).op,
    { rw [this, pow_succ], simp },
    simp_rw ← helper.op_comp,
    congr' 1,
    change _ ≫ (cech_obj f).δ _ = (cech_obj f).δ _ ≫ _,
    convert cech_splitting_face f g splitting n _ _,
    simp,
    exact fin.succ_ne_zero _ }
end

-- The contracting homotopy in degree -1
theorem is_contracting_homotopy_zero :
  (conerve_complex f M).d 0 1 ≫ contracting_homotopy f M g splitting 0 +
  M.map ((augmentation_obj_iso f).hom ≫ f ≫ g ≫ (augmentation_obj_iso f).inv).op = 𝟙 _ :=
begin
  delta conerve_complex,
  dsimp only [cosimplicial_object.cocomplex, cosimplicial_object.to_cocomplex, cochain_complex.mk'],
  split_ifs,
  swap, finish,
  dsimp only [cosimplicial_object.coboundary],
  simp only [preadditive.sum_comp, fin.sum_univ_succ, fin.default_eq_zero],
  simp only [category_theory.category.comp_id,
    add_zero,
    fin.coe_zero,
    fin.sum_univ_zero,
    fin.coe_one,
    one_gsmul,
    category_theory.eq_to_hom_refl,
    category_theory.functor.comp_map,
    --category_theory.cech_obj_map,
    fin.coe_succ,
    category_theory.op_comp,
    neg_gsmul,
    pow_one,
    fin.succ_zero_eq_one,
    category_theory.category.assoc,
    category_theory.functor.right_op_map,
    category_theory.functor.map_comp,
    pow_zero,
    finset.sum_congr,
    category_theory.preadditive.add_comp,
    category_theory.preadditive.neg_comp],
  delta contracting_homotopy,
  simp_rw ← M.map_comp,
  rw ← add_zero (𝟙 _),
  swap, apply_instance,
  rw add_assoc,
  congr' 1,
  { erw ← M.map_id,
    congr' 1,
    simp_rw ← helper.op_comp,
    dsimp only [functor.right_op],
    change _ = (𝟙 _).op,
    congr' 1,
    tidy
    },
  { rw neg_add_eq_zero,
    congr' 1,
    simp_rw ← helper.op_comp,
    congr' 1,
    dsimp only [augmentation_obj_iso],
    ext,
    simp,
    split_ifs,
    { refl },
    { exfalso,
      apply h_1,
      apply_fun equiv.ulift,
      change fin.succ_above _ j.down = 0,
      rw fin.succ_above_below,
      sorry,
      sorry },
    simp [splitting],
  }
end

end cech

end category_theory
