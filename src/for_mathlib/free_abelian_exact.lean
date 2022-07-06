import for_mathlib.AddCommGroup.exact
import for_mathlib.free_abelian_group2

noncomputable theory

open category_theory
open_locale big_operators

variables (A : Type*) [add_comm_group A]

namespace free_abelian_group

def σπ : free_abelian_group (A × A) →+ free_abelian_group A :=
free_abelian_group.map prod.fst + free_abelian_group.map prod.snd -
free_abelian_group.map (function.uncurry (+))

lemma σπ_of (x) : σπ A (of x) = (of x.1) + (of x.2) - of (x.1 + x.2) :=
by simp only [σπ, add_monoid_hom.sub_apply, add_monoid_hom.add_apply, map_of_apply, function.uncurry]

lemma σπ_comp_zero : AddCommGroup.of_hom (σπ A) ≫ AddCommGroup.of_hom (lift id) = 0 :=
begin
  ext ⟨x,y⟩,
  simp only [comp_apply, AddCommGroup.of_hom_apply, σπ_of, _root_.map_sub, _root_.map_add,
    lift.of, id.def, sub_self, AddCommGroup.zero_apply],
end

section norm

variables {X : Type*} (a b : free_abelian_group X)

def norm : ℕ := ∑ x in a.support, (coeff x a).nat_abs

-- SELFCONTAINED
@[simp] lemma norm_of (x : X) : (of x).norm = 1 := sorry

-- SELFCONTAINED
lemma norm_add : (a + b).norm ≤ a.norm + b.norm := sorry

-- SELFCONTAINED
@[simp] lemma norm_neg : (-a).norm = a.norm := sorry

-- SELFCONTAINED
lemma norm_sub : (a - b).norm ≤ a.norm + b.norm := sorry

-- SELFCONTAINED
@[simp] lemma norm_eq_zero_iff : a.norm = 0 ↔ a = 0 := sorry

lemma norm_eq_succ_iff (n : ℕ) :
  a.norm = n.succ ↔ ∃ b x, (a = b + of x ∨ a = b - of x) ∧ b.norm = n :=
sorry

-- SELFCONTAINED
lemma norm_eq_one_iff : a.norm = 1 ↔ ∃ x, a = of x ∨ a = -of x :=
sorry

end norm

lemma σπ_of_00 : σπ A (of (0,0)) = of 0 :=
by simp only [σπ_of, add_zero, add_sub_cancel']

lemma exact_σπ_induction (a : free_abelian_group A) (ha : free_abelian_group.lift id a = 0)
  (n : ℕ) (hn : a.norm ≤ n) :
  ∃ x, free_abelian_group.σπ A x = a :=
begin
  induction n with n ih generalizing a,
  { simp only [nat.le_zero_iff, norm_eq_zero_iff] at hn, subst a, exact ⟨0, _root_.map_zero _⟩ },
  erw [nat.le_add_one_iff] at hn, cases hn with hn hn, { exact ih a ha hn },
  cases n,
  { rw [norm_eq_one_iff] at hn, rcases hn with ⟨a, (rfl|rfl)⟩,
    all_goals { simp only [lift.of, _root_.map_neg, _root_.id, neg_eq_zero] at ha, subst a, },
    { exact ⟨of (0,0), σπ_of_00 _⟩ },
    { refine ⟨-of (0,0), _⟩, rw [_root_.map_neg, σπ_of_00] } },
  rw norm_eq_succ_iff at hn, rcases hn with ⟨b, y, H1, hn⟩,
  rw norm_eq_succ_iff at hn, rcases hn with ⟨c, x, H2, hn⟩,
  rcases H1 with (rfl|rfl); rcases H2 with (rfl|rfl),
  { obtain ⟨p, hp⟩ := ih (c + of (x+y)) _ _, rotate,
    { simpa only [lift.of, _root_.map_add, id.def, add_assoc] using ha, },
    { refine (norm_add _ _).trans _, rw [hn, norm_of], },
    refine ⟨p + of (x,y), _⟩,
    simp only [_root_.map_add, hp, σπ_of, add_assoc, add_right_inj],
    rw [add_comm (of (x+y)), sub_add_cancel], },
  { obtain ⟨p, hp⟩ := ih (c + of (y-x)) _ _, rotate,
    { simpa only [lift.of, _root_.map_add, _root_.map_neg, id.def,
        add_assoc, sub_eq_add_neg, add_comm y] using ha, },
    { refine (norm_add _ _).trans _, rw [hn, norm_of], },
    refine ⟨p - of (y-x,x), _⟩,
    simp only [_root_.map_add, _root_.map_neg, sub_eq_add_neg, hp, σπ_of,
      neg_add_cancel_right, neg_add_rev, neg_neg, add_assoc,
      add_left_neg, add_zero, add_right_inj],
    rw [add_comm (of (y+-x)), add_comm _ (of y)],
    simp only [add_assoc, add_left_neg, add_zero], },
  { obtain ⟨p, hp⟩ := ih (c + of (x-y)) _ _, rotate,
    { simpa only [lift.of, _root_.map_add, _root_.map_neg, id.def,
        add_assoc, sub_eq_add_neg] using ha, },
    { refine (norm_add _ _).trans _, rw [hn, norm_of], },
    refine ⟨p - of (x-y,y), _⟩,
    simp only [_root_.map_add, _root_.map_neg, sub_eq_add_neg, hp, σπ_of,
      neg_add_cancel_right, neg_add_rev, neg_neg, add_assoc, add_right_inj,
      add_left_neg, add_zero],
    rw [add_comm (of (x+-y))],
    simp only [add_assoc, add_left_neg, add_zero], },
  { obtain ⟨p, hp⟩ := ih (c - of (x+y)) _ _, rotate,
    { simpa only [lift.of, _root_.map_add, _root_.map_neg, id.def, neg_add,
        add_assoc, sub_eq_add_neg] using ha, },
    { refine (norm_sub _ _).trans _, rw [hn, norm_of], },
    refine ⟨p - of (x,y), _⟩,
    simp only [_root_.map_add, _root_.map_neg, sub_eq_add_neg, hp, σπ_of,
      neg_add_cancel_right, neg_add_rev, neg_neg, add_assoc, neg_add_cancel_left],
    rw add_comm (-of x) },
end

lemma exact_σπ : exact
  (AddCommGroup.of_hom $ free_abelian_group.σπ A)
  (AddCommGroup.of_hom $ free_abelian_group.lift id) :=
begin
  rw AddCommGroup.exact_iff',
  refine ⟨σπ_comp_zero _, _⟩,
  intros a ha,
  obtain ⟨p, hp⟩ := exact_σπ_induction A a ha a.norm le_rfl,
  exact ⟨p, hp⟩
end

end free_abelian_group
