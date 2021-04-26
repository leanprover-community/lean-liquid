import algebra.module.pi
import algebra.big_operators

open_locale big_operators

section for_mathlib

-- can be removed, I guess
@[simp] lemma function.nsmul_apply {X M : Type*} [add_comm_monoid M]
  (n : ℕ) (f : X → M) (x : X) :
  (n • f) x = n • (f x) :=
by rw [pi.smul_apply]

@[simp, to_additive] lemma monoid_hom.coe_one {M₁ M₂ : Type*} [monoid M₁] [monoid M₂] :
  ⇑(1 : M₁ →* M₂) = 1 := rfl

@[simp, to_additive] lemma monoid_hom.coe_mul {M₁ M₂ : Type*} [monoid M₁] [comm_monoid M₂]
  (f g : M₁ →* M₂) :
  ⇑(f * g) = f * g := rfl

@[simp, to_additive] lemma monoid_hom.coe_div {M₁ M₂ : Type*} [monoid M₁] [comm_group M₂]
  (f g : M₁ →* M₂) :
  ⇑(f / g) = f / g := rfl

@[simp, to_additive] lemma monoid_hom.coe_inv {M₁ M₂ : Type*} [monoid M₁] [comm_group M₂]
  (f : M₁ →* M₂) :
  ⇑(f⁻¹) = f⁻¹ := rfl

@[simp] lemma add_monoid_hom.coe_nsmul {M₁ M₂ : Type*} [add_monoid M₁] [add_comm_monoid M₂]
  (n : ℕ) (f : M₁ →+ M₂) :
  ⇑(n • f) = n • (f : M₁ → M₂) :=
begin
  induction n with n ih,
  { simp only [add_monoid_hom.zero_apply, zero_nsmul, add_monoid_hom.coe_zero], },
  { simp only [succ_nsmul, add_monoid_hom.coe_add, ih] }
end

@[simp] lemma function.gsmul_apply {X M : Type*} [add_comm_group M]
  (n : ℤ) (f : X → M) (x : X) :
  (n • f) x = n • (f x) :=
begin
  apply int.induction_on n,
  { simp only [zero_gsmul, pi.zero_apply] },
  { simp only [add_gsmul, function.nsmul_apply, forall_const, pi.add_apply,
      one_gsmul, eq_self_iff_true, gsmul_coe_nat] },
  { intro, simp only [sub_gsmul, neg_gsmul, forall_prop_of_true, function.nsmul_apply,
      pi.neg_apply, one_gsmul, gsmul_coe_nat, pi.sub_apply (-(i • f)) f x] }
end

@[simp] lemma add_monoid_hom.coe_gsmul {M₁ M₂ : Type*} [add_monoid M₁] [add_comm_group M₂]
  (n : ℤ) (f : M₁ →+ M₂) :
  ⇑(n • f) = n • (f : M₁ → M₂) :=
begin
  apply int.induction_on n,
  { simp only [zero_gsmul, add_monoid_hom.coe_zero] },
  { simp only [add_monoid_hom.coe_nsmul, gsmul_coe_nat, add_gsmul,
      forall_const, one_gsmul, eq_self_iff_true, add_monoid_hom.coe_add] },
  { simp only [forall_prop_of_true, gsmul_coe_nat, sub_gsmul, neg_gsmul, one_gsmul, neg_gsmul,
      add_monoid_hom.coe_neg, add_monoid_hom.coe_nsmul, add_monoid_hom.coe_sub,
      eq_self_iff_true, forall_const] }
end

end for_mathlib

namespace add_monoid_hom

variables {M₁ M₂ : Type*}

section
variables [add_monoid M₁] [add_comm_monoid M₂]

@[simp] lemma sum_apply {ι : Type*} (s : finset ι) (f : ι → (M₁ →+ M₂)) (m : M₁) :
  (∑ i in s, f i) m = ∑ i in s, (f i m) :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [finset.sum_empty, zero_apply] },
  { intros i s his IH, simp only [his, IH, finset.sum_insert, not_false_iff, add_apply] }
end

end

section
variables [add_monoid M₁] [add_comm_group M₂]

@[simp] lemma gsmul_apply (n : ℤ) (f : (M₁ →+ M₂)) (m : M₁) :
  (n • f) m = n • (f m) :=
show eval m (n • f) = n • eval m f, from add_monoid_hom.map_gsmul _ _ _

end

end add_monoid_hom
#lint- only unused_arguments def_lemma doc_blame
