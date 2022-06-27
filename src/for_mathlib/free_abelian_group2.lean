import group_theory.free_abelian_group_finsupp
import for_mathlib.free_abelian_group

namespace free_abelian_group

lemma lift_map {A B C : Type*} [add_comm_group C]
  (f : A → B) (g : B → C) (x) :
  free_abelian_group.lift g (free_abelian_group.map f x) =
  free_abelian_group.lift (g ∘ f) x :=
begin
  rw [← add_monoid_hom.comp_apply], congr' 1, clear x, ext x,
  simp only [add_monoid_hom.coe_comp, function.comp_app, map_of_apply, free_abelian_group.lift.of, id.def]
end

lemma lift_id_map {A B : Type*} [add_comm_group B]
  (f : A → B) (x) :
  free_abelian_group.lift id (free_abelian_group.map f x) =
  free_abelian_group.lift f x :=
free_abelian_group.lift_map _ _ _

open_locale big_operators

lemma coeff_of_not_mem_support
  {X : Type*} (a : free_abelian_group X) (x : X) (h : x ∉ a.support) :
  free_abelian_group.coeff x a = 0 :=
begin
  dsimp [free_abelian_group.coeff],
  rwa [← finsupp.not_mem_support_iff],
end

lemma lift_eq_sum {A B : Type*} [add_comm_group B]
  (f : A → B) (x) :
  free_abelian_group.lift f x = ∑ a in x.support, free_abelian_group.coeff a x • f a :=
begin
  apply free_abelian_group.induction_on'' x; clear x,
  { simp only [add_monoid_hom.map_zero, zero_smul, finset.sum_const_zero], },
  { intros n hn a,
    simp only [map_zsmul, smul_assoc, ← finset.smul_sum,
      free_abelian_group.lift.of, support_zsmul n hn, support_of, finset.sum_singleton,
      coeff_of_self, one_smul], },
  { intros x n hn a hax IH1 IH2, specialize IH2 n,
    simp only [add_monoid_hom.map_add, map_zsmul, smul_assoc, free_abelian_group.lift.of,
      support_add_smul_of x n hn a hax, support_zsmul n hn,
      support_of, finset.sum_singleton] at IH2 ⊢,
    rw [finset.sum_insert], swap, exact hax,
    simp only [IH1, coeff_of_self, smul_assoc, one_smul, add_smul,
      finset.sum_add_distrib, coeff_of_not_mem_support _ _ hax,
      zero_smul, zero_add],
    rw add_comm, refine congr_arg2 _ rfl _, symmetry, convert add_zero _,
    rw finset.sum_eq_zero,
    intros z hz,
    rw [coeff_of_not_mem_support, zero_smul, smul_zero],
    rw [support_of, finset.mem_singleton], rintro rfl, exact hax hz }
end

end free_abelian_group
