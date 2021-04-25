import .split
import for_mathlib.simplicial.complex

open_locale big_operators

noncomputable theory

namespace category_theory

namespace cech

universes v u

variables {P : Type v} {C : Type u} [small_category P] [category.{v} C] [preadditive C]
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
    sorry }
end

end cech

end category_theory
