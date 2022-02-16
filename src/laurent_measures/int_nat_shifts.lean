import topology.algebra.infinite_sum
import analysis.normed_space.basic
import topology.instances.ennreal
import analysis.specific_limits

/- These are lemmas that are used in the proof of either auxilliary facts for Theorem 6.9 or
for Theorem 6.9 directly. -/

open function metric finset nnreal normed_field
open_locale nnreal classical big_operators topological_space

namespace aux_thm69

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
  int_subtype_nonneg_equiv z = int.to_nat z :=
begin
  rcases z with ⟨x | y, hz⟩,
  { refl },
  { exact ((int.neg_succ_not_nonneg _).mp hz).elim }
end

@[simp]
lemma int.to_nat_subtype_nonneg {z : {x : ℤ // 0 ≤ x}} :
  ((z : ℤ).to_nat : ℤ) = z :=
begin
  cases z with x hz,
  simp [int.to_nat_of_nonneg hz],
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
  refine summable.congr ‹_› (λ b, _);
  simp only [oppo_symm_eval, int_subtype_nonneg_equiv_eval, function.comp_app];
  { apply congr_arg, simp [b.2] }
end

end uniform

lemma _root_.summable.smaller_radius {f : ℕ → ℝ} {ρ σ : ℝ≥0}
  (hf : summable (λ n, f n * ρ ^ n)) (σρ : σ ≤ ρ) (f0 : ∀ n, 0 ≤ f n) :
  summable (λ n, f n * σ ^ n) :=
begin
  refine summable_of_nonneg_of_le (λ b, mul_nonneg (f0 _) (pow_nonneg zero_le_coe _)) _ hf,
  exact λ b, mul_le_mul rfl.le
    (pow_le_pow_of_le_left zero_le_coe σρ b) (pow_nonneg zero_le_coe b) (f0 b)
end

/--  A technical equivalence, useful in the proof of `prod_nat_summable_1`. -/
def equiv_nat_diag : {x : ℕ × ℕ // x.2 ≤ x.1} ≃ ℕ × ℕ :=
{ to_fun    := λ x, (x.1.1 - x.1.2, x.1.2 ),
  inv_fun   := λ x, ⟨(x.1 + x.2, x.2), by simp⟩,
  left_inv  := by { rintros ⟨x, hx⟩, simp only [nat.sub_add_cancel hx, prod.mk.eta] },
  right_inv := by { rintros ⟨x, y⟩, simp only [add_tsub_cancel_right] } }

lemma _root_.summable.prod_nat {f : ℤ → ℝ} {g : ℕ → ℝ} (hf : summable f) (f0 : ∀ n, 0 ≤ f n)
  (hg : summable g) (g0 : ∀ n, 0 ≤ g n) :
  summable (λ lj: ℕ × ℕ, f (lj.fst + lj.snd) * g lj.snd) :=
begin
  apply (equiv.summable_iff equiv_nat_diag).mp,
  suffices : summable (λ (lj : {x : ℕ × ℕ // x.2 ≤ x.1}), f lj.1.fst * g lj.1.snd),
  { convert this,
    ext ⟨⟨x, y⟩, hx⟩,
    suffices : f (↑(x - y) + ↑y) * g y = f ↑x * g y, by simpa [equiv_nat_diag],
    rw_mod_cast nat.sub_add_cancel hx },
  apply summable.subtype (_ : summable (λ (lj : ℕ × ℕ), f lj.fst * g lj.snd)),
  convert summable_mul_of_summable_norm (_ : summable (λ i : ℕ, ∥f i∥)) _,
  { conv { congr, funext, rw [real.norm_of_nonneg (f0 _)] },
    apply ((int_summable_iff).mp hf).1 },
  { conv { congr, funext, rw [real.norm_of_nonneg (g0 _)] },
    exact hg }
end

lemma prod_nat_summable_aux {f : ℤ → ℝ} {s r : ℝ≥0}
  (s1 : s < 1) (hf : summable (λ n : ℤ, ∥ f n ∥ * r ^ n)) :
  summable (λ lj: ℕ × ℕ, ∥(f (lj.fst + 1 + lj.snd)) * r ^ (lj.fst + 1 + lj.snd)∥ * s^ lj.snd) :=
begin
  apply summable_of_summable_norm,
  simp_rw [norm_mul, norm_norm],
  convert (_ : summable (λ n, ∥f (n + 1)∥ * r ^ (n + 1))).prod_nat _ (by simpa) (pow_nonneg s.2),
  { simpa only [norm_pow, norm_eq, val_eq_coe, add_right_comm _ (1 : ℤ), add_right_comm _ 1 _] },
  { let add_one : ℤ ≃ ℤ := ⟨λ x, x - 1, λ x, x + 1, λ x, by simp, λ x, by simp⟩,
    apply add_one.summable_iff.mp,
    convert hf,
    ext,
    simp },
  { exact λ n, mul_nonneg (norm_nonneg _) (zpow_nonneg r.2 _) },
end

end aux_thm69
