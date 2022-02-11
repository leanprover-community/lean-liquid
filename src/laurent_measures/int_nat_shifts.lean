import topology.algebra.infinite_sum
import analysis.normed_space.basic
import topology.instances.ennreal

open function
open metric finset nnreal
open_locale nnreal classical big_operators topological_space

section group_add_neg
variables {G : Type*} [group G] [has_le G] [covariant_class G G ((*)) (≤)]

@[to_additive]
lemma aux_ineq_mul {d e x : G} (hx : d ≤ x) : e ≤ e * d⁻¹ * x :=
calc  e ≤ e * (d⁻¹ * x) : le_mul_of_one_le_right' (le_inv_mul_iff_le.mpr hx)
    ... = e * d⁻¹ * x   : (mul_assoc _ _ _).symm

/--  If `G` is a group and `d e : G`. then `mul_inv_fun d e` is the function mapping
`{x // d ≤ x}` to `{x // e ≤ x}` defined by `x ↦ e * d⁻¹ * x`. -/
@[to_additive "If `G` is an additive group and `d e : G`. then `add_neg_fun d e` is the function
mapping `{x // d ≤ x}` to `{x // e ≤ x}` defined by `x ↦ e + (- d) + x`."]
def mul_inv_fun (d e : G) : {x // d ≤ x} → {x // e ≤ x} :=
λ ⟨x, hx⟩, ⟨_, aux_ineq_mul hx⟩

@[to_additive]
lemma mul_inv_fun_def (d e : G) (z : {x // d ≤ x}) :
  mul_inv_fun d e z = ⟨_, aux_ineq_mul z.2⟩ :=
by { cases z, simp [mul_inv_fun] }

@[simp, to_additive]
lemma mul_inv_fun_comp (d e f : G) : mul_inv_fun e f ∘ mul_inv_fun d e = mul_inv_fun d f :=
by { funext, simp [mul_inv_fun_def, mul_assoc] }

@[simp, to_additive]
lemma mul_inv_fun_comp_id (d e : G) : mul_inv_fun e d ∘ mul_inv_fun d e = id :=
by { funext, simp [mul_inv_fun_def] }

@[simp, to_additive]
lemma mul_inv_fun_comp_id_apply (d e : G) (z : {x // d ≤ x}) :
  mul_inv_fun e d (mul_inv_fun d e z) = z :=
by simp [mul_inv_fun_def, mul_assoc]

/--  The function `mul_inv_fun d e` bundled as an equivalence `{x // d ≤ x} ≃ {x // e ≤ x}`. -/
@[to_additive "The function `add_neg_fun d e` bundled as an equivalence
`{x // d ≤ x} ≃ {x // e ≤ x}`."]
def equiv.mul_inv (d e : G) : {x // d ≤ x} ≃ {x // e ≤ x} :=
{ to_fun    := mul_inv_fun d e,
  inv_fun   := mul_inv_fun e d,
  left_inv  := λ z, by simp,
  right_inv := λ z, by simp }

@[simp, to_additive]
lemma equiv.mul_inv_eval (d e : G) (x : {x // d ≤ x}) :
  equiv.mul_inv d e x = ⟨e * d⁻¹ * x, aux_ineq_mul x.2⟩ :=
by { cases x with x hx, simpa }

@[simp, to_additive]
lemma equiv.mul_inv_rev (d e : G) :
  (equiv.mul_inv d e).symm = equiv.mul_inv e d := rfl

end group_add_neg

/--  The subtype of nonnegative integers is equivalent to the natural number. -/
def int_subtype_nonneg_equiv : {x : ℤ // 0 ≤ x} ≃ ℕ :=
{ to_fun := begin
    rintro ⟨x | y, hx⟩,
    { exact x },
    { exact ((int.neg_succ_not_nonneg _).mp hx).elim }
  end,
  inv_fun := λ x, ⟨x, int.coe_zero_le x⟩,
  left_inv := begin
    rintro ⟨x | y, hx⟩,
    { simp only [int.of_nat_eq_coe, subtype.coe_mk] },
    { exact ((int.neg_succ_not_nonneg _).mp hx).elim }
  end,
  right_inv := λ x, rfl }

@[simp]
lemma int_subtype_nonneg_equiv_eval {z : {x : ℤ // 0 ≤ x}} :
  (int_subtype_nonneg_equiv z : ℤ) = z :=
begin
  rcases z with ⟨x | y, hz⟩,
  { refl },
  { exact ((int.neg_succ_not_nonneg _).mp hz).elim }
end

@[simp]
lemma int_subtype_nonneg_equiv_symm_eval {n : ℕ} : (int_subtype_nonneg_equiv.symm n : ℤ) = n := rfl

/--  The subtype of nonnegative integers is equivalent to the natural number. -/
def int.nonneg_equiv_nat (d : ℤ) : {x : ℤ // d ≤ x} ≃ ℕ :=
(equiv.add_neg d 0).trans int_subtype_nonneg_equiv

/--  The subtype of nonnegative integers is equivalent to the natural number. -/
def nat.le_equiv_nat (d : ℕ) : {x // d ≤ x} ≃ ℕ :=
{ to_fun    := λ x, x.1 - d,
  inv_fun   := λ x, ⟨x + d, le_add_self⟩,
  left_inv  := by { rintro ⟨x, hx⟩, simp only [nat.sub_add_cancel hx] },
  right_inv := λ x, by simp }

/--  The "identity" is an equivalence between the complement of the set of non-negative integers
and the negative integers. -/
def compl_le : ↥(set_of ((≤) (0 : ℤ)))ᶜ ≃ {z : ℤ // z < 0} :=
{ to_fun    := by { rintro ⟨a, ha⟩, exact ⟨a, by simpa using ha⟩ },
  inv_fun   := by { rintro ⟨a, ha⟩, exact ⟨a, by simpa using ha⟩ },
  left_inv  := by { rintro ⟨a, ha⟩, simp },
  right_inv := by { rintro ⟨a, ha⟩, simp } }

@[simp]
lemma compl_le_symm_eval {x : {z : ℤ // z < 0}} :
  (compl_le.symm x : ℤ) = x :=
by { cases x with x hx, refl }

section group_one_one
variables (α : Type*) [group α] [has_lt α] [covariant_class α α (*) (<)]

/--  Taking inverses establishes an isomorphism between the elements of a group that are
strictly smaller than `1` with the elements that are strictly larger than `1`. -/
@[to_additive "Taking opposites establishes an isomorphism between the elements of an additive
group that are strictly smaller than `0` with the elements that are strictly larger than `0`."]
def equiv.lt_one_gt_one : {z : α | z < 1} ≃ {z : α | 1 < z} :=
{ to_fun    := by { rintro ⟨z, hz⟩, exact ⟨z⁻¹, by simpa⟩ },
  inv_fun   := by { rintro ⟨z, hz⟩, exact ⟨z⁻¹, by simpa⟩ },
  left_inv  := by { rintro ⟨z, hz⟩, simp },
  right_inv := by { rintro ⟨z, hz⟩, simp } }

variable {α}

@[simp, to_additive]
lemma equiv.lt_one_gt_one_eval {x : {z : α | z < 1}} :
  ((equiv.lt_one_gt_one α) x : α) = x⁻¹ :=
by { cases x with x hx, refl }

@[simp, to_additive]
lemma equiv.lt_one_gt_one_symm_eval {x : {z : α | 1 < z}} :
  ((equiv.lt_one_gt_one α).symm x : α) = x⁻¹ :=
by { cases x with x hx, refl }

end group_one_one

/--  An equivalence between the complement of the non-negative integers and the natural numbers. -/
def oppo : ({z : ℤ | 0 ≤ z}ᶜ : set ℤ) ≃ ℕ :=
compl_le.trans $ (equiv.neg_gt_zero ℤ).trans $ (equiv.add_neg 1 0).trans int_subtype_nonneg_equiv

@[simp]
lemma oppo_symm_eval {n : ℕ} : (oppo.symm n : ℤ) = - n - 1 :=
by simp [oppo]

section topological_space
variables {α : Type*} [topological_space α]

section add_comm_monoid
variables [add_comm_monoid α] {f : ℤ → α}

lemma my_summable_shift (f : ℤ → α) (N : ℤ) :
  summable (λ x : ℕ, f (x + N)) ↔ summable (λ x : {x // N ≤ x}, f x) :=
begin
  convert (int_subtype_nonneg_equiv.symm.trans (equiv.add_neg 0 N)).summable_iff,
  ext,
  simp [add_comm],
end

end add_comm_monoid

end topological_space

section uniform
variables {α : Type*} [uniform_space α] [add_comm_group α] [uniform_add_group α] [complete_space α]
variable {f : ℤ → α}

lemma int_summable_iff :
  summable f ↔ summable (λ n : ℕ, f n) ∧ summable (λ n : ℕ, f (- n - 1)) :=
begin
  refine (@summable_subtype_and_compl α _ _ _ _ _ _ {z : ℤ | 0 ≤ z}).symm.trans _,
  rw [← equiv.summable_iff int_subtype_nonneg_equiv, ← equiv.summable_iff oppo.symm],
  refine ⟨_, _⟩;
  rintro ⟨h1, h2⟩;
  refine ⟨_, _⟩;
  exact summable.congr ‹_› (λ b,
    by simp only [oppo_symm_eval, int_subtype_nonneg_equiv_eval, function.comp_app]),
end

end uniform

lemma summable_smaller_radius {f : ℕ → ℝ} {ρ σ : ℝ≥0}
  (σρ : σ ≤ ρ) (f0 : ∀ n, 0 ≤ f n) (hf : summable (λ n, f n * ρ ^ n)) :
  summable (λ n, f n * σ ^ n) :=
begin
  refine summable_of_nonneg_of_le (λ b, mul_nonneg (f0 _) (pow_nonneg zero_le_coe _)) _ hf,
  exact λ b, mul_le_mul rfl.le
    (pow_le_pow_of_le_left zero_le_coe σρ b) (pow_nonneg zero_le_coe b) (f0 b)
end
