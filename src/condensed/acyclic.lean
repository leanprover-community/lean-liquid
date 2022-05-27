import for_mathlib.derived.Ext_lemmas
import for_mathlib.Cech.homotopy
import for_mathlib.acyclic
import for_mathlib.exact_seq4

import condensed.projective_resolution
.

noncomputable theory

universes u

open category_theory category_theory.limits homotopy_category opposite
open function (surjective)

lemma projective_of_iso {𝓐 : Type*} [category 𝓐] {X Y : 𝓐} (e : X ≅ Y) (h : projective X) :
  projective Y :=
sorry

namespace condensed

def free_Cech' (F : arrow Profinite.{u}) :
  chain_complex (Condensed.{u} Ab.{u+1}) ℕ :=
(((simplicial_object.augmented.whiskering _ _).obj
  (Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab)).obj
  F.augmented_cech_nerve).to_complex

def free_Cech (F : arrow Profinite.{u}) :
  chain_complex (Condensed.{u} Ab.{u+1}) ℤ :=
(homological_complex.embed $ complex_shape.embedding.nat_down_int_down).obj (free_Cech' F)

lemma free_Cech_exact (F : arrow Profinite.{u}) (n : ℤ) :
  is_zero $ (free_Cech F).homology n :=
sorry

-- lemma free_Cech'_SES_0 (F : arrow Profinite.{u}) :
--   short_exact (kernel.ι $ (free_Cech' F).d (-1) 0) ((free_Cech' F).d 0 1) :=
-- begin
--   suffices : epi ((free_Cech' F).d 0 1), { resetI, refine ⟨exact_kernel_ι⟩, },
-- end

lemma free_Cech_kernel_SES (F : arrow Profinite.{u}) : ∀ n,
  short_exact (kernel.ι $ (free_Cech F).d (n+1+1) (n+1)) (delta_to_kernel _ (n+1+1) (n+1) n) :=
begin
  erw ← is_acyclic_iff_short_exact_to_cycles' (free_Cech F), exact free_Cech_exact F
end

def arrow.cech_nerve_obj_0 (F : arrow Profinite) :
  F.cech_nerve.obj (op (simplex_category.mk 0)) ≅ F.left :=
sorry

variable (M : Condensed.{u} Ab.{u+1})

abbreviation HH (i : ℤ) (S : Profinite.{u}) (M : Condensed.{u} Ab.{u+1}) :=
((Ext' i).obj (op $ (CondensedSet_to_Condensed_Ab).obj $ Profinite.to_Condensed S)).obj M

def acyclic_of_exact.IH (n : ℤ) : Prop := ∀ S, ∀ i > 0, i ≤ n → is_zero (HH i S M)

lemma acyclic_of_exact.induction_step
  (h : ∀ (F : arrow Profinite.{u}) (surj : function.surjective F.hom),
    ∀ i, is_zero
    (((((cosimplicial_object.augmented.whiskering _ _).obj M.val).obj
      F.augmented_cech_nerve.right_op).to_cocomplex).homology i))
  (n : ℤ) (ih : acyclic_of_exact.IH M n) :
  acyclic_of_exact.IH M (n+1) :=
begin
  intros S i h1 h2,
  rw [le_iff_eq_or_lt, or_comm, int.lt_add_one_iff] at h2,
  cases h2 with h2 h2, { exact ih S i h1 h2 },
  subst i,
  let F := arrow.mk S.projective_presentation.f,
  let E := λ i, (Ext' i).flip.obj M,
  have ih' : ∀ (i j : ℤ) (h0i : 0 < i) (hin : i ≤ n),
    is_zero ((E i).obj (op ((free_Cech F).X j))),
  { intros i j h0i hin,
    cases j with j j,
    { cases j; exact ih _ _ h0i hin, },
    { apply bounded_derived_category.Ext'_zero_left_is_zero,
      exact (is_zero_zero _).op, } },
  let K := λ i, kernel ((free_Cech F).d (i + 1) i),
  have aux0 : ∀ (i : ℤ) (h0i : 0 < i) (H : is_zero ((E (i+1)).obj (op $ K (-1)))),
    is_zero ((E i).obj (op $ K 0)),
  { intros i h0i H,
    have SES := (free_Cech_kernel_SES F (-1)).Ext'_five_term_exact_seq M i,
    refine is_zero_of_exact_is_zero_is_zero _ _ (SES.drop 1).pair _ H, clear SES,
    apply bounded_derived_category.Ext'_is_zero_of_projective _ _ _ _ h0i,
    apply_with Condensed_Ab.free.category_theory.projective {instances:=ff},
    rw [simplicial_object.augmented.drop_obj, arrow.augmented_cech_nerve_left],
    apply projective_of_iso (arrow.cech_nerve_obj_0 F).symm,
    apply projective_presentation.projective, },
  have aux : ∀ (i j : ℤ) (h0i : 0 < i) (hi : i ≤ n) (H : is_zero ((E (i+1)).obj (op $ K j))),
    is_zero ((E i).obj (op $ K (j+1))),
  { intros i j h0i hi H,
    have SES := (free_Cech_kernel_SES F j).Ext'_five_term_exact_seq M i,
    refine is_zero_of_exact_is_zero_is_zero _ _ (SES.drop 1).pair _ H,
    refine ih' i _ h0i _, sorry, },
  suffices : ∀ i j, 0 < i → i + j ≤ n → is_zero ((E i).obj (op $ K j)),
  { have SES := (free_Cech_kernel_SES F (-2)).Ext'_five_term_exact_seq M (n+1),
    refine is_zero_of_exact_is_zero_is_zero _ _ SES.pair _ _; clear SES,
    { refine this (n+1) (-2) h1 _, sorry },
    { refine this (n+1) (-1) h1 _, sorry } },
  intros i j h0i,
  apply int.induction_on' j (-2); clear j,
  { intro hjn,
    apply bounded_derived_category.Ext'_zero_left_is_zero,
    refine (is_zero_of_mono (kernel.ι _) _).op, refine is_zero_zero _, },
  { intros j hj IH hijn,
    rw [le_iff_eq_or_lt] at hj, cases hj with hj hj,
    { subst j, sorry },
    apply aux _ _ h0i, sorry, sorry },
  -- induction j with j j, swap,
  sorry
end

lemma acyclic_of_exact
  (h : ∀ (F : arrow Profinite.{u}) (surj : function.surjective F.hom),
    ∀ i, is_zero
    (((((cosimplicial_object.augmented.whiskering _ _).obj M.val).obj
      F.augmented_cech_nerve.right_op).to_cocomplex).homology i))
  (S : Profinite.{u}) :
  ∀ i > 0, is_zero (HH i S M)  :=
begin
  intros i hi,
  suffices : acyclic_of_exact.IH M i,
  { apply this S i hi le_rfl, },
  apply int.induction_on' i 0; clear hi i S,
  { intros S i h1 h2, exfalso, exact h2.not_lt h1 },
  { intros k hk, apply acyclic_of_exact.induction_step M h, },
  { rintros k hk aux S i h1 h2, exfalso, linarith only [hk, h1, h2] }
end

end condensed
