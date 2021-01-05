import data.real.nnreal
import algebra.group.hom
import algebra.big_operators
import algebra.module.pi

import type_pow

noncomputable theory

open_locale nnreal big_operators

local attribute [instance] type_pow

section for_mathlib

@[simp] lemma function.nsmul_apply {X M : Type*} [add_comm_monoid M]
  (n : ℕ) (f : X → M) (x : X) :
  (n •ℕ f) x = n •ℕ (f x) :=
by rw [semimodule.nsmul_eq_smul ℕ, semimodule.nsmul_eq_smul ℕ, nat.cast_id, pi.smul_apply]

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

attribute [instance] pseudo_normed_group.to_add_comm_group

namespace pseudo_normed_group

variables {M : Type*} [pseudo_normed_group M]

lemma sub_mem_filtration ⦃c₁ c₂ x₁ x₂⦄ (h₁ : x₁ ∈ filtration M c₁) (h₂ : x₂ ∈ filtration M c₂) :
  x₁ - x₂ ∈ filtration M (c₁ + c₂) :=
by { rw [sub_eq_add_neg], exact add_mem_filtration h₁ (neg_mem_filtration h₂) }

lemma neg_mem_filtration_iff (c x) : -x ∈ filtration M c ↔ x ∈ filtration M c :=
⟨λ h, by { rw [← neg_neg x], exact neg_mem_filtration h }, λ h, neg_mem_filtration h⟩

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

section

set_option old_structure_cmd true

structure pseudo_normed_group_hom (M₁ M₂ : Type*) [pseudo_normed_group M₁] [pseudo_normed_group M₂]
  extends M₁ →+ M₂ :=
(bound : ℝ≥0)
(map_mem_filtration' : ∀ ⦃c x⦄, x ∈ filtration M₁ c → to_fun x ∈ filtration M₂ (bound * c))

end

namespace pseudo_normed_group_hom

variables {M M₁ M₂ M₃ : Type*}
variables [pseudo_normed_group M] [pseudo_normed_group M₁]
variables [pseudo_normed_group M₂] [pseudo_normed_group M₃]
variables (f g : pseudo_normed_group_hom M₁ M₂)

instance : has_coe_to_fun (pseudo_normed_group_hom M₁ M₂) := ⟨_, pseudo_normed_group_hom.to_fun⟩

@[simp] lemma coe_mk (f) (h₁) (h₂) (C) (h₃) :
  ⇑(⟨f, h₁, h₂, C, h₃⟩ : pseudo_normed_group_hom M₁ M₂) = f := rfl

@[simp] lemma mk_to_add_monoid_hom (f) (h₁) (h₂) (C) (h₃) :
  (⟨f, h₁, h₂, C, h₃⟩ : pseudo_normed_group_hom M₁ M₂).to_add_monoid_hom = ⟨f, h₁, h₂⟩ := rfl

@[simp] lemma coe_to_add_monoid_hom (f : pseudo_normed_group_hom M₁ M₂) :
  ⇑f.to_add_monoid_hom = f := rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

lemma map_mem_filtration ⦃c x⦄ (h : x ∈ filtration M₁ c) : f x ∈ filtration M₂ (f.bound * c) :=
f.map_mem_filtration' h

@[ext] theorem ext (H : ∀ x, f x = g x) (H' : f.bound = g.bound) : f = g :=
by cases f; cases g; congr'; exact funext H

def mk' (f : M₁ →+ M₂) (C : ℝ≥0) (hC : ∀ c x, x ∈ filtration M₁ c → f x ∈ filtration M₂ (C * c)) :
  pseudo_normed_group_hom M₁ M₂ :=
{ bound := C, map_mem_filtration' := hC, .. f}

@[simp] lemma coe_mk' (f : M₁ →+ M₂) (C) (hC) : ⇑(mk' f C hC) = f := rfl

instance : has_zero (pseudo_normed_group_hom M₁ M₂) :=
⟨mk' (0 : M₁ →+ M₂) 0 $ by intros; exact zero_mem_filtration _⟩

instance : inhabited (pseudo_normed_group_hom M₁ M₂) := ⟨0⟩

@[simps]
def id : pseudo_normed_group_hom M M :=
{ bound := 1,
  map_mem_filtration' := λ c x h,
    by simpa only [one_mul, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.id_apply] using h,
  .. add_monoid_hom.id M }

instance : has_one (pseudo_normed_group_hom M M) := ⟨id⟩

lemma one_def : (1 : pseudo_normed_group_hom M M) = id := rfl

@[simps]
def comp (g : pseudo_normed_group_hom M₂ M₃) (f : pseudo_normed_group_hom M₁ M₂) :
  pseudo_normed_group_hom M₁ M₃ :=
{ bound := g.bound * f.bound,
  map_mem_filtration' := λ c x h,
  begin
    simp only [add_monoid_hom.coe_comp, add_monoid_hom.to_fun_eq_coe, function.comp_app, mul_assoc],
    exact g.map_mem_filtration (f.map_mem_filtration h)
  end,
  .. g.to_add_monoid_hom.comp f.to_add_monoid_hom }

private def add (f g : pseudo_normed_group_hom M₁ M₂) : pseudo_normed_group_hom M₁ M₂ :=
mk' (f.to_add_monoid_hom + g.to_add_monoid_hom) (f.bound + g.bound)
begin
  intros c x h, rw add_mul,
  exact add_mem_filtration (f.map_mem_filtration h) (g.map_mem_filtration h)
end

private def neg (f : pseudo_normed_group_hom M₁ M₂) : pseudo_normed_group_hom M₁ M₂ :=
mk' (-f.to_add_monoid_hom) f.bound $ λ c x h, neg_mem_filtration (f.map_mem_filtration h)

instance : has_neg (pseudo_normed_group_hom M₁ M₂) := ⟨neg⟩

private def sub (f g : pseudo_normed_group_hom M₁ M₂) : pseudo_normed_group_hom M₁ M₂ :=
mk' (f.to_add_monoid_hom - g.to_add_monoid_hom) (f.bound + g.bound)
begin
  intros c x h, rw add_mul,
  exact sub_mem_filtration (f.map_mem_filtration h) (g.map_mem_filtration h)
end

instance : has_sub (pseudo_normed_group_hom M₁ M₂) := ⟨sub⟩

/-
Because of our unorthodox choice of bundling `bound`
into the definition of `pseudo_normed_group_hom`,
we cannot get an `add_comm_group` structure on `pseudo_normed_group_hom`:
we can't get `f + (-f) = 0` because the RHS has a bound that is typically nonzero.
-/

instance : add_comm_monoid (pseudo_normed_group_hom M₁ M₂) :=
{ zero := 0,
  add := add,
  add_assoc := by { intros, ext; exact add_assoc _ _ _ },
  zero_add := by { intros, ext; exact zero_add _ },
  add_zero := by { intros, ext; exact add_zero _ },
  add_comm := by { intros, ext; exact add_comm _ _ } }

@[simp] lemma bound_id : (id : pseudo_normed_group_hom M M).bound = 1 := rfl

@[simp] lemma bound_one : (1 : pseudo_normed_group_hom M M).bound = 1 := rfl

@[simp] lemma bound_comp (g : pseudo_normed_group_hom M₂ M₃) (f : pseudo_normed_group_hom M₁ M₂) :
  (g.comp f).bound = g.bound * f.bound := rfl

@[simp] lemma bound_zero : (0 : pseudo_normed_group_hom M₁ M₂).bound = 0 := rfl

@[simp] lemma bound_add : (f + g).bound = f.bound + g.bound := rfl

@[simp] lemma bound_neg : (-f).bound = f.bound := rfl

@[simp] lemma bound_sub : (f - g).bound = f.bound + g.bound := rfl

@[simp] lemma bound_sum {ι : Type*} (f : ι → pseudo_normed_group_hom M₁ M₂) (s : finset ι) :
  (∑ i in s, f i).bound = ∑ i in s, (f i).bound :=
begin
  classical,
  apply finset.induction_on s; clear s,
  { simp only [bound_zero, finset.sum_empty] },
  { intros i s his IH,
    simp only [IH, his, bound_add, finset.sum_insert, not_false_iff] }
end

@[simp] lemma coe_id : ⇑(id : pseudo_normed_group_hom M M) = id := rfl

@[simp] lemma coe_one : ⇑(1 : pseudo_normed_group_hom M M) = id := rfl

@[simp] lemma coe_comp (g : pseudo_normed_group_hom M₂ M₃) (f : pseudo_normed_group_hom M₁ M₂) :
  ⇑(g.comp f) = g ∘ f := rfl

@[simp] lemma coe_zero : ⇑(0 : pseudo_normed_group_hom M₁ M₂) = 0 := rfl

@[simp] lemma coe_add : ⇑(f + g) = f + g := rfl

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl

@[simp] lemma coe_sub : ⇑(f - g) = f - g := rfl

@[simp] lemma coe_sum {ι : Type*} (f : ι → pseudo_normed_group_hom M₁ M₂) (s : finset ι) :
  ⇑(∑ i in s, f i) = ∑ i in s, (f i) :=
begin
  classical,
  apply finset.induction_on s; clear s,
  { simp only [finset.sum_empty, coe_zero] },
  { intros i s his IH,
    simp only [IH, his, coe_add, finset.sum_insert, not_false_iff] }
end

@[simp] protected lemma neg_zero : -(0 : pseudo_normed_group_hom M₁ M₂) = 0 :=
by { ext; simp only [coe_zero, coe_neg, neg_zero, bound_neg] }

@[simp] protected lemma neg_neg : - -(f : pseudo_normed_group_hom M₁ M₂) = f :=
by { ext; simp only [coe_neg, neg_neg, bound_neg] }

def to_add_monoid_hom_hom : pseudo_normed_group_hom M₁ M₂ →+ (M₁ →+ M₂) :=
{ to_fun := to_add_monoid_hom,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

@[simps {rhs_md:=semireducible, fully_applied:=ff}]
def mk_to_pi {ι : Type*} [fintype ι] {M : ι → Type*} [Π i, pseudo_normed_group (M i)]
  (f : Π i, pseudo_normed_group_hom M₁ (M i)) :
  pseudo_normed_group_hom M₁ (Π i, M i) :=
mk'
{ to_fun := λ v i, f i v,
  map_zero' := by { simp only [map_zero], refl },
  map_add' := by { intros, simp only [map_add], refl } }
(finset.univ.sup (λ i, (f i).bound))
begin
  intros c x h i,
  simp only [add_monoid_hom.coe_mk],
  refine filtration_mono _ ((f i).map_mem_filtration h),
  apply mul_le_mul_of_nonneg_right _ (zero_le c),
  exact finset.le_sup (finset.mem_univ i)
end

@[simps {rhs_md:=semireducible, fully_applied:=ff}]
def apply {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)] (i : ι) :
  pseudo_normed_group_hom (Π i, M i) (M i) :=
mk' (add_monoid_hom.apply M i) 1 $
λ c x h, by { rw [one_mul], exact (h i) }

@[simp] lemma bound_apply {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)] (i : ι) :
  (apply M i).bound = 1 := rfl

def mk_from_pi {ι : Type*} [fintype ι] {M : ι → Type*} [Π i, pseudo_normed_group (M i)]
  (f : Π i, pseudo_normed_group_hom (M i) M₂) :
  pseudo_normed_group_hom (Π i, M i) M₂ :=
∑ i, (f i).comp (apply M i)

@[simp] lemma bound_mk_from_pi {ι : Type*} [fintype ι] {M : ι → Type*}
  [Π i, pseudo_normed_group (M i)] (f : Π i, pseudo_normed_group_hom (M i) M₂) :
  (mk_from_pi f).bound = ∑ i, (f i).bound :=
by simp only [mk_from_pi, bound_sum, bound_apply, mul_one, bound_comp]

@[simp] lemma coe_mk_from_pi {ι : Type*} [fintype ι] {M : ι → Type*} [Π i, pseudo_normed_group (M i)]
  (f : Π i, pseudo_normed_group_hom (M i) M₂) :
  ⇑(mk_from_pi f) = ∑ i, (f i ∘ apply M i) :=
begin
  ext x,
  simp only [apply_to_fun, add_monoid_hom.apply_apply, add_monoid_hom.to_fun_eq_coe,
    fintype.sum_apply, function.comp_app],
  show add_monoid_hom.eval x (to_add_monoid_hom_hom (mk_from_pi f)) = _,
  simp only [mk_from_pi, add_monoid_hom.map_sum],
  refl
end

def nsmul : ℕ →+ pseudo_normed_group_hom M M := nat.cast_add_monoid_hom _

@[simp] protected lemma nsmul_one : (nsmul 1 : pseudo_normed_group_hom M M) = id := nat.cast_one

@[simp] lemma coe_nsmul (n : ℕ) :
  ⇑(nsmul n : pseudo_normed_group_hom M M) = λ x, n • x :=
begin
  ext,
  induction n with n ih,
  { simp only [coe_zero, pi.zero_apply, zero_smul, add_monoid_hom.map_zero] },
  { simp only [ih, nat.succ_eq_add_one, add_monoid_hom.map_add, pi.add_apply, id_to_fun,
      add_monoid_hom.to_fun_eq_coe, add_monoid_hom.id_apply, coe_add, add_smul, one_smul,
      pseudo_normed_group_hom.nsmul_one] }
end

@[simp] lemma bound_nsmul (n : ℕ) : (nsmul n : pseudo_normed_group_hom M M).bound = n :=
begin
  induction n with n ih,
  { simp only [bound_zero, nat.cast_zero, add_monoid_hom.map_zero] },
  { simp only [ih, nat.succ_eq_add_one, bound_add, add_monoid_hom.map_add, bound_id,
      add_left_inj, nat.cast_add, nat.cast_one, pseudo_normed_group_hom.nsmul_one] }
end

def gsmul : ℤ → pseudo_normed_group_hom M M
| (n:ℕ)  := nsmul n
| -[1+n] := -nsmul (n+1)

@[simp] protected lemma gsmul_zero : (gsmul 0 : pseudo_normed_group_hom M M) = 0 :=
nsmul.map_zero

@[simp] protected lemma gsmul_one : (gsmul 1 : pseudo_normed_group_hom M M) = id :=
pseudo_normed_group_hom.nsmul_one

@[simp] protected lemma gsmul_nat (n : ℕ) : (gsmul n : pseudo_normed_group_hom M M) = nsmul n := rfl

@[simp] protected lemma gsmul_neg_succ_of_nat (n : ℕ) :
  (gsmul (-[1+n]) : pseudo_normed_group_hom M M) = -nsmul (n+1) := rfl

@[simp] lemma gsmul_neg : ∀ n, (gsmul (-n) : pseudo_normed_group_hom M M) = -gsmul n
| (0:ℕ)   := pseudo_normed_group_hom.neg_zero.symm
| (n+1:ℕ) := rfl
| -[1+n]  := (pseudo_normed_group_hom.neg_neg _).symm

@[simp] lemma coe_gsmul : ∀ n, ⇑(gsmul n : pseudo_normed_group_hom M M) = λ x, n • x
| (0:ℕ)   := by simpa only [zero_smul] using pseudo_normed_group_hom.gsmul_zero
| (n+1:ℕ) := coe_nsmul _
| -[1+n]  := show ⇑(-nsmul (n+1) : pseudo_normed_group_hom M M) = λ x, -[1+n] • x,
by { simp only [coe_neg, coe_nsmul, int.neg_succ_of_nat_coe], refl }

@[simp] lemma bound_gsmul : ∀ n, (gsmul n : pseudo_normed_group_hom M M).bound = n.nat_abs
| (0:ℕ)   := rfl
| (n+1:ℕ) := bound_nsmul _
| -[1+n]  :=
calc (gsmul -[1+n]).bound
    = (nsmul (n+1)).bound : bound_neg _
... = (n+1)               : bound_nsmul _

end pseudo_normed_group_hom
