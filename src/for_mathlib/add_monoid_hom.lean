import algebra.module.pi
import algebra.big_operators

open_locale big_operators

variables {M₁ M₂ : Type*}

namespace monoid_hom

variable [monoid M₁]

@[simp, to_additive] lemma coe_one [monoid M₂] : ⇑(1 : M₁ →* M₂) = 1 := rfl

@[simp, to_additive] lemma coe_mul [comm_monoid M₂] (f g : M₁ →* M₂) :
  ⇑(f * g) = f * g := rfl

@[simp, to_additive] lemma coe_div [comm_group M₂] (f g : M₁ →* M₂) :
  ⇑(f / g) = f / g := rfl

@[simp, to_additive] lemma coe_inv [comm_group M₂] (f : M₁ →* M₂) :
  ⇑(f⁻¹) = f⁻¹ := rfl

end monoid_hom

namespace add_monoid_hom

variable [add_monoid M₁]

@[simp] lemma coe_nsmul [add_comm_monoid M₂] (n : ℕ) (f : M₁ →+ M₂) :
  ⇑(n • f) = n • (f : M₁ → M₂) := rfl

@[simp] lemma coe_gsmul [add_comm_group M₂] (n : ℤ) (f : M₁ →+ M₂) :
  ⇑(n • f) = n • (f : M₁ → M₂) := rfl

@[simp] lemma nsmul_apply [add_comm_monoid M₂] (n : ℕ) (f : (M₁ →+ M₂)) (m : M₁) :
  (n • f) m = n • (f m) := rfl

@[simp] lemma gsmul_apply [add_comm_group M₂] (n : ℤ) (f : (M₁ →+ M₂)) (m : M₁) :
  (n • f) m = n • (f m) := rfl

end add_monoid_hom

#lint- only unused_arguments def_lemma doc_blame
