import data.real.nnreal
import algebra.group.hom
import algebra.big_operators
import algebra.module.pi
import topology.basic

import hacks_and_tricks.type_pow

noncomputable theory

open_locale nnreal big_operators

local attribute [instance] type_pow

section for_mathlib

@[simp] lemma function.nsmul_apply {X M : Type*} [add_comm_monoid M]
  (n : ℕ) (f : X → M) (x : X) :
  (n •ℕ f) x = n •ℕ (f x) :=
by rw [nsmul_eq_smul, nsmul_eq_smul, pi.smul_apply]

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
  ⇑(n •ℕ f) = n •ℕ (f : M₁ → M₂) :=
begin
  induction n with n ih,
  { simp only [add_monoid_hom.zero_apply, zero_nsmul, add_monoid_hom.coe_zero], },
  { simp only [succ_nsmul, add_monoid_hom.coe_add, ih] }
end

@[simp] lemma function.gsmul_apply {X M : Type*} [add_comm_group M]
  (n : ℤ) (f : X → M) (x : X) :
  (n •ℤ f) x = n •ℤ (f x) :=
begin
  apply int.induction_on n,
  { simp only [zero_gsmul, pi.zero_apply] },
  { simp only [add_gsmul, function.nsmul_apply, forall_const, pi.add_apply,
      one_gsmul, eq_self_iff_true, gsmul_coe_nat] },
  { intro, simp only [sub_gsmul, neg_gsmul, forall_prop_of_true, function.nsmul_apply,
      pi.neg_apply, one_gsmul, gsmul_coe_nat, pi.sub_apply (-(i •ℕ f)) f x] }
end

@[simp] lemma add_monoid_hom.coe_gsmul {M₁ M₂ : Type*} [add_monoid M₁] [add_comm_group M₂]
  (n : ℤ) (f : M₁ →+ M₂) :
  ⇑(n •ℤ f) = n •ℤ (f : M₁ → M₂) :=
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

/-- See top of p66 in [Analytic.pdf]. -/
class pseudo_normed_group (M : Type*) :=
[to_add_comm_group : add_comm_group M]
(filtration [] : ℝ≥0 → set M)
(filtration_mono : ∀ ⦃c₁ c₂⦄, c₁ ≤ c₂ → filtration c₁ ⊆ filtration c₂)
(zero_mem_filtration : ∀ c, (0:M) ∈ filtration c)
(neg_mem_filtration : ∀ ⦃c x⦄, x ∈ filtration c → (-x) ∈ filtration c)
(add_mem_filtration : ∀ ⦃c₁ c₂ x₁ x₂⦄,
  x₁ ∈ filtration c₁ → x₂ ∈ filtration c₂ → x₁ + x₂ ∈ filtration (c₁ + c₂))

open function

class pseudo_normed_group' (B_ : ℝ≥0 → Type*) (M : out_param Type*) :=
[to_add_comm_group : add_comm_group M]
[has_zero : Π r, has_zero (B_ r)]
[has_neg : Π r, has_neg (B_ r)]
(map : ∀ ⦃c₁ c₂⦄, c₁ ≤ c₂ → B_ c₁ → B_ c₂) -- rename
(incl : ∀ c, B_ c → M)
(incl_injective : ∀ c, injective (incl c))
(incl_zero : ∀ c, incl c 0 = 0)
(incl_neg : ∀ {c} (f : B_ c), incl c (-f) = - (incl c f))
(incl_map : ∀ {c₁ c₂} (h : c₁ ≤ c₂), (incl c₂) ∘ (map h) = (incl c₁))
(B_add {c₁ c₂} : B_ c₁ → B_ c₂ → B_ (c₁ + c₂))
(incl_add {c₁ c₂} (f : B_ c₁) (g : B_ c₂) : incl _ (B_add f g) = incl _ f + incl _ g)
(map_refl {c} : map (le_refl c) = id)
(map_trans {c₁ c₂ c₃} (h1 : c₁ ≤ c₂) (h2 : c₂ ≤ c₃) : map (h1.trans h2) = map h2 ∘ map h1)

/-
class topological_pseudo_normed_group' (B_ : ℝ≥0 → Type*) (M : Type*)
  extends pseudo_normed_group' B_ M :=
[is_top_space : Π r, topological_space (B_ r)]
-/


/-
Thought by Johan:
Maybe we want both defintions above, and write a bit of glue to move between them.
Both seem useful for different bits of what we want to do.
-/

attribute [instance] pseudo_normed_group.to_add_comm_group

namespace pseudo_normed_group

variables {M : Type*} [pseudo_normed_group M]

lemma sub_mem_filtration ⦃c₁ c₂ x₁ x₂⦄ (h₁ : x₁ ∈ filtration M c₁) (h₂ : x₂ ∈ filtration M c₂) :
  x₁ - x₂ ∈ filtration M (c₁ + c₂) :=
by { rw [sub_eq_add_neg], exact add_mem_filtration h₁ (neg_mem_filtration h₂) }

lemma neg_mem_filtration_iff (c x) : -x ∈ filtration M c ↔ x ∈ filtration M c :=
⟨λ h, by { rw [← neg_neg x], exact neg_mem_filtration h }, λ h, neg_mem_filtration h⟩

lemma sum_mem_filtration {ι : Type*} (x : ι → M) (c : ι → ℝ≥0) (s : finset ι)
  (h : ∀ i ∈ s, x i ∈ filtration M (c i)) :
  (∑ i in s, x i) ∈ filtration M (∑ i in s, (c i)) :=
begin
  classical,
  revert h, apply finset.induction_on s; clear s,
  { intro, simpa only [finset.sum_empty] using zero_mem_filtration _ },
  { intros i s his IH h,
    rw [finset.sum_insert his, finset.sum_insert his],
    apply add_mem_filtration (h _ _) (IH _),
    { exact finset.mem_insert_self i s },
    { intros j hj, apply h, exact finset.mem_insert_of_mem hj } }
end

lemma smul_nat_mem_filtration (n : ℕ) (x : M) (c : ℝ≥0) (hx : x ∈ filtration M c) :
  n • x ∈ filtration M (n * c) :=
begin
  induction n with n ih,
  { simpa only [nat.cast_zero, zero_mul, zero_smul] using zero_mem_filtration _ },
  { simp only [nat.succ_eq_add_one, add_smul, one_smul, nat.cast_succ, add_mul, one_mul],
    exact add_mem_filtration ih hx }
end

lemma smul_int_mem_filtration (n : ℤ) (x : M) (c : ℝ≥0) (hx : x ∈ filtration M c) :
  n • x ∈ filtration M (n.nat_abs * c) :=
begin
  induction n with n n,
  { exact smul_nat_mem_filtration n x c hx },
  { rw [int.nat_abs_of_neg_succ_of_nat, int.neg_succ_of_nat_coe, neg_smul, neg_mem_filtration_iff],
    exact smul_nat_mem_filtration _ _ _ hx }
end

instance pi {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)] :
  pseudo_normed_group (Π i, M i) :=
{ filtration := λ c, { x | ∀ i, x i ∈ filtration (M i) c }, -- TODO: check with Peter
  filtration_mono := λ c₁ c₂ h x hx i, filtration_mono h (hx i),
  zero_mem_filtration := λ c i, zero_mem_filtration _,
  neg_mem_filtration := λ c x h i, neg_mem_filtration (h i),
  add_mem_filtration := λ c₁ c₂ x₁ x₂ h₁ h₂ i, add_mem_filtration (h₁ i) (h₂ i) }

lemma mem_filtration_pi {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)]
  (c : ℝ≥0) (x : Π i, M i) :
  x ∈ filtration (Π i, M i) c ↔ ∀ i, x i ∈ filtration (M i) c := iff.rfl

end pseudo_normed_group

open pseudo_normed_group

namespace add_monoid_hom

variables {M M₁ M₂ M₃ : Type*}
variables [pseudo_normed_group M] [pseudo_normed_group M₁]
variables [pseudo_normed_group M₂] [pseudo_normed_group M₃]

instance : pseudo_normed_group (M₁ →+ M₂) :=
{ filtration := λ N, { f | ∀ ⦃c⦄ ⦃x : M₁⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ (N * c) },
  filtration_mono := λ N₁ N₂ h f hf c x hx, filtration_mono (mul_le_mul_right' h c) (hf hx),
  zero_mem_filtration := λ N c x hx, zero_mem_filtration _,
  neg_mem_filtration := λ N f hf c x hx, neg_mem_filtration $ hf hx,
  add_mem_filtration := λ N₁ N₂ f₁ f₂ hf₁ hf₂ c x hx,
  by { rw add_mul, apply add_mem_filtration (hf₁ hx) (hf₂ hx) },
  .. add_monoid_hom.add_comm_group }

lemma comp_mem_filtration {g f cg cf}
  (hg : g ∈ filtration (M₂ →+ M₃) cg) (hf : f ∈ filtration (M₁ →+ M₂) cf) :
  g.comp f ∈ filtration (M₁ →+ M₃) (cg * cf) :=
λ c x hx, by { rw mul_assoc, exact hg (hf hx) }

@[simp] lemma id_mem_filtration (c : ℝ≥0) (hc : 1 ≤ c) : id M ∈ filtration (M →+ M) c :=
λ c' x hx, by refine filtration_mono _ hx;
calc c' = 1 * c' : by rw one_mul
    ... ≤ c * c' : mul_le_mul_right' hc c'

-- move this, maybe it already exists?
@[simps {rhs_md:=semireducible, fully_applied:=ff}]
def mk_to_pi {M₁} [add_monoid M₁] {ι : Type*} {M : ι → Type*} [Π i, add_monoid (M i)]
  (f : Π i, M₁ →+ (M i)) :
  M₁ →+ (Π i, M i) :=
{ to_fun := λ v i, f i v,
  map_zero' := by { simp only [map_zero], refl },
  map_add' := by { intros, simp only [map_add], refl } }

lemma mk_to_pi_mem_filtration {ι : Type*} {M : ι → Type*}
  [Π i, pseudo_normed_group (M i)] (f : Π i, M₁ →+ (M i))
  {c} (hfc : ∀ i, f i ∈ filtration (M₁ →+ (M i)) c) :
  mk_to_pi f ∈ filtration (M₁ →+ (Π i, M i)) c :=
λ c' x h i, hfc i h

lemma apply_mem_filtration {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)]
  (i : ι) (c : ℝ≥0) (hc : 1 ≤ c) :
  (apply M i) ∈ filtration ((Π i, M i) →+ M i) c :=
λ c' x hx, by refine filtration_mono _ (hx i);
calc c' = 1 * c' : by rw one_mul
    ... ≤ c * c' : mul_le_mul_right' hc c'

def mk_from_pi {ι : Type*} [fintype ι] {M : ι → Type*} {M₂}
  [Π i, add_monoid (M i)] [add_comm_monoid M₂] (f : Π i, (M i) →+ M₂) :
  (Π i, M i) →+ M₂ :=
∑ i, (f i).comp (apply M i)

@[simp] lemma mk_from_pi_apply {ι : Type*} [fintype ι] {M : ι → Type*} [Π i, add_comm_monoid (M i)]
  (f : Π i, M i →+ M₂) (x : Π i, M i) :
  mk_from_pi f x = (∑ i, f i (x i)) :=
begin
  show add_monoid_hom.eval x (mk_from_pi f) = _,
  simp only [mk_from_pi, add_monoid_hom.map_sum],
  refl
end

@[simp] lemma coe_mk_from_pi {ι : Type*} [fintype ι] {M : ι → Type*} [Π i, add_comm_monoid (M i)]
  (f : Π i, M i →+ M₂) :
  ⇑(mk_from_pi f) = ∑ i, (f i ∘ apply M i) :=
by { ext x, rw [@mk_from_pi_apply M₂ _ ι _ M _ f x, fintype.sum_apply], refl }

lemma mk_from_pi_mem_filtration {ι : Type*} [fintype ι] {M : ι → Type*}
  [Π i, pseudo_normed_group (M i)] (f : Π i, (M i) →+ M₂)
  {c : ι → ℝ≥0} (hfc : ∀ i, f i ∈ filtration ((M i) →+ M₂) (c i)) :
  (mk_from_pi f) ∈ filtration ((Π i, M i) →+ M₂) (∑ i, c i) :=
λ c' x h,
begin
  rw [finset.sum_mul, @mk_from_pi_apply M₂ _ ι _ M _ f x],
  refine sum_mem_filtration _ _ _ _,
  rintro i -,
  exact hfc i (h i)
end

lemma const_smul_hom_nat_mem_filtration (n : ℕ) (c : ℝ≥0) (h : ↑n ≤ c) :
  const_smul_hom M n ∈ filtration (M →+ M) c :=
λ c' x hx, by simpa only [const_smul_hom_apply]
  using filtration_mono (mul_le_mul_right' h c') (smul_nat_mem_filtration _ _ _ hx)

lemma const_smul_hom_int_mem_filtration (n : ℤ) (c : ℝ≥0) (h : ↑(n.nat_abs) ≤ c) :
  const_smul_hom M n ∈ filtration (M →+ M) c :=
λ c' x hx, by simpa only [const_smul_hom_apply]
  using filtration_mono (mul_le_mul_right' h c') (smul_int_mem_filtration _ _ _ hx)

end add_monoid_hom
