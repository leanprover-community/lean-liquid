import algebra.linear_ordered_comm_group_with_zero
import algebra.big_operators.ring
import data.real.basic
import data.indicator_function
import algebra.algebra.basic

/-!
# Nonnegative rationals
-/

noncomputable theory

open_locale classical big_operators

/-- Nonnegative rational numbers. -/
def nnrat := {q : ℚ // 0 ≤ q}
localized "notation ` ℚ≥0 ` := nnrat" in nnreal

namespace nnrat

instance : has_coe ℚ≥0 ℚ := ⟨subtype.val⟩

/- Simp lemma to put back `n.val` into the normal form given by the coercion. -/
@[simp] lemma val_eq_coe (n : ℚ≥0) : n.val = n := rfl

instance : can_lift ℚ ℚ≥0 :=
{ coe := coe,
  cond := λ r, 0 ≤ r,
  prf := λ x hx, ⟨⟨x, hx⟩, rfl⟩ }

protected lemma eq {n m : ℚ≥0} : (n : ℚ) = (m : ℚ) → n = m := subtype.eq

protected lemma eq_iff {n m : ℚ≥0} : (n : ℚ) = (m : ℚ) ↔ n = m :=
iff.intro nnrat.eq (congr_arg coe)

lemma ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y :=
not_iff_not_of_iff $ nnrat.eq_iff

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q < 0`. -/
protected def of_rat (q : ℚ) : ℚ≥0 := ⟨max q 0, le_max_right _ _⟩

lemma coe_of_rat (q : ℚ) (hr : 0 ≤ q) : (nnrat.of_rat q : ℚ) = q :=
max_eq_left hr

lemma le_coe_of_rat (r : ℚ) : r ≤ nnrat.of_rat r :=
le_max_left r 0

lemma coe_nonneg (r : ℚ≥0) : (0 : ℚ) ≤ r := r.2
@[norm_cast]
theorem coe_mk (a : ℚ) (ha) : ((⟨a, ha⟩ : ℚ≥0) : ℚ) = a := rfl

instance : has_zero ℚ≥0  := ⟨⟨0, le_refl 0⟩⟩
instance : has_one ℚ≥0   := ⟨⟨1, zero_le_one⟩⟩
instance : has_add ℚ≥0   := ⟨λa b, ⟨a + b, add_nonneg a.2 b.2⟩⟩
instance : has_sub ℚ≥0   := ⟨λa b, nnrat.of_rat (a - b)⟩
instance : has_mul ℚ≥0   := ⟨λa b, ⟨a * b, mul_nonneg a.2 b.2⟩⟩
instance : has_inv ℚ≥0   := ⟨λa, ⟨(a.1)⁻¹, inv_nonneg.2 a.2⟩⟩
instance : has_div ℚ≥0   := ⟨λa b, ⟨a / b, div_nonneg a.2 b.2⟩⟩
instance : has_le ℚ≥0    := ⟨λ r s, (r:ℚ) ≤ s⟩
instance : has_bot ℚ≥0   := ⟨0⟩
instance : inhabited ℚ≥0 := ⟨0⟩

protected lemma coe_injective : function.injective (coe : ℚ≥0 → ℚ) := subtype.coe_injective
@[simp, norm_cast] protected lemma coe_eq {r₁ r₂ : ℚ≥0} : (r₁ : ℚ) = r₂ ↔ r₁ = r₂ :=
nnrat.coe_injective.eq_iff
@[simp, norm_cast] protected lemma coe_zero : ((0 : ℚ≥0) : ℚ) = 0 := rfl
@[simp, norm_cast] protected lemma coe_one  : ((1 : ℚ≥0) : ℚ) = 1 := rfl
@[simp, norm_cast] protected lemma coe_add (r₁ r₂ : ℚ≥0) : ((r₁ + r₂ : ℚ≥0) : ℚ) = r₁ + r₂ := rfl
@[simp, norm_cast] protected lemma coe_mul (r₁ r₂ : ℚ≥0) : ((r₁ * r₂ : ℚ≥0) : ℚ) = r₁ * r₂ := rfl
@[simp, norm_cast] protected lemma coe_inv (r : ℚ≥0) : ((r⁻¹ : ℚ≥0) : ℚ) = r⁻¹ := rfl
@[simp, norm_cast] protected lemma coe_div (r₁ r₂ : ℚ≥0) : ((r₁ / r₂ : ℚ≥0) : ℚ) = r₁ / r₂ := rfl
@[simp, norm_cast] protected lemma coe_bit0 (r : ℚ≥0) : ((bit0 r : ℚ≥0) : ℚ) = bit0 r := rfl
@[simp, norm_cast] protected lemma coe_bit1 (r : ℚ≥0) : ((bit1 r : ℚ≥0) : ℚ) = bit1 r := rfl

@[simp, norm_cast] protected lemma coe_sub {r₁ r₂ : ℚ≥0} (h : r₂ ≤ r₁) :
  ((r₁ - r₂ : ℚ≥0) : ℚ) = r₁ - r₂ :=
max_eq_left $ le_sub.2 $ by simp [show (r₂ : ℚ) ≤ r₁, from h]

-- TODO: setup semifield!
@[simp] protected lemma coe_eq_zero (r : ℚ≥0) : ↑r = (0 : ℚ) ↔ r = 0 := by norm_cast
lemma coe_ne_zero {r : ℚ≥0} : (r : ℚ) ≠ 0 ↔ r ≠ 0 := by norm_cast

instance : comm_semiring ℚ≥0 :=
{ zero := 0,
  add := (+),
  one := 1,
  mul := (*),
  .. nnrat.coe_injective.comm_semiring _ rfl rfl (λ _ _, rfl) (λ _ _, rfl) }

/-- Coercion `ℚ≥0 → ℚ` as a `ring_hom`. -/
def to_rational_hom : ℚ≥0 →+* ℚ :=
⟨coe, nnrat.coe_one, nnrat.coe_mul, nnrat.coe_zero, nnrat.coe_add⟩

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : algebra ℚ≥0 ℚ := to_rational_hom.to_algebra

@[simp] lemma coe_to_rational_hom : ⇑to_rational_hom = coe := rfl

instance : comm_group_with_zero ℚ≥0 :=
{ zero := 0,
  mul := (*),
  one := 1,
  inv := has_inv.inv,
  div := (/),
  .. nnrat.coe_injective.comm_group_with_zero _ rfl rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) }

@[simp, norm_cast] lemma coe_indicator {α} (s : set α) (f : α → ℚ≥0) (a : α) :
  ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (λ x, f x) a :=
(to_rational_hom : ℚ≥0 →+ ℚ).map_indicator _ _ _

@[simp, norm_cast] lemma coe_pow (r : ℚ≥0) (n : ℕ) : ((r^n : ℚ≥0) : ℚ) = r^n :=
to_rational_hom.map_pow r n

@[norm_cast] lemma coe_list_sum (l : list ℚ≥0) :
  ((l.sum : ℚ≥0) : ℚ) = (l.map coe).sum :=
to_rational_hom.map_list_sum l

@[norm_cast] lemma coe_list_prod (l : list ℚ≥0) :
  ((l.prod : ℚ≥0) : ℚ) = (l.map coe).prod :=
to_rational_hom.map_list_prod l

@[norm_cast] lemma coe_multiset_sum (s : multiset ℚ≥0) :
  ((s.sum : ℚ≥0) : ℚ) = (s.map coe).sum :=
to_rational_hom.map_multiset_sum s

@[norm_cast] lemma coe_multiset_prod (s : multiset ℚ≥0) :
  ((s.prod : ℚ≥0) : ℚ) = (s.map coe).prod :=
to_rational_hom.map_multiset_prod s

@[norm_cast] lemma coe_sum {α} {s : finset α} {f : α → ℚ≥0} :
  ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
to_rational_hom.map_sum _ _

lemma of_rat_sum_of_nonneg {α} {s : finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  nnrat.of_rat (∑ a in s, f a) = ∑ a in s, nnrat.of_rat (f a) :=
begin
  rw [←nnrat.coe_eq, nnrat.coe_sum, nnrat.coe_of_rat _ (finset.sum_nonneg hf)],
  exact finset.sum_congr rfl (λ x hxs, by rw nnrat.coe_of_rat _ (hf x hxs)),
end

@[norm_cast] lemma coe_prod {α} {s : finset α} {f : α → ℚ≥0} :
  ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
to_rational_hom.map_prod _ _

lemma of_rat_prod_of_nonneg {α} {s : finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  nnrat.of_rat (∏ a in s, f a) = ∏ a in s, nnrat.of_rat (f a) :=
begin
  rw [←nnrat.coe_eq, nnrat.coe_prod, nnrat.coe_of_rat _ (finset.prod_nonneg hf)],
  exact finset.prod_congr rfl (λ x hxs, by rw nnrat.coe_of_rat _ (hf x hxs)),
end

@[norm_cast] lemma nsmul_coe (r : ℚ≥0) (n : ℕ) : ↑(n • r) = n • (r:ℚ) :=
to_rational_hom.to_add_monoid_hom.map_nsmul _ _

@[simp, norm_cast] protected lemma coe_nat_cast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n :=
to_rational_hom.map_nat_cast n

instance : linear_order ℚ≥0 :=
linear_order.lift (coe : ℚ≥0 → ℚ) nnrat.coe_injective

@[simp, norm_cast] protected lemma coe_le_coe {r₁ r₂ : ℚ≥0} : (r₁ : ℚ) ≤ r₂ ↔ r₁ ≤ r₂ := iff.rfl
@[simp, norm_cast] protected lemma coe_lt_coe {r₁ r₂ : ℚ≥0} : (r₁ : ℚ) < r₂ ↔ r₁ < r₂ := iff.rfl
@[simp, norm_cast] protected lemma coe_pos {r : ℚ≥0} : (0 : ℚ) < r ↔ 0 < r := iff.rfl

protected lemma coe_mono : monotone (coe : ℚ≥0 → ℚ) := λ _ _, nnrat.coe_le_coe.2

protected lemma of_rat_mono : monotone nnrat.of_rat :=
λ x y h, max_le_max h (le_refl 0)

@[simp] lemma of_rat_coe {r : ℚ≥0} : nnrat.of_rat r = r :=
nnrat.eq $ max_eq_left r.2

@[simp] lemma mk_coe_nat (n : ℕ) : @eq ℚ≥0 (⟨(n : ℚ), n.cast_nonneg⟩ : ℚ≥0) n :=
nnrat.eq (nnrat.coe_nat_cast n).symm

@[simp] lemma of_rat_coe_nat (n : ℕ) : nnrat.of_rat n = n :=
nnrat.eq $ by simp [coe_of_rat]

/-- `nnrat.of_rat` and `coe : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : galois_insertion nnrat.of_rat coe :=
galois_insertion.monotone_intro nnrat.coe_mono nnrat.of_rat_mono
  le_coe_of_rat (λ _, of_rat_coe)

instance : order_bot ℚ≥0 :=
{ bot := ⊥, bot_le := assume ⟨a, h⟩, h, .. nnrat.linear_order }

instance : canonically_linear_ordered_add_monoid ℚ≥0 :=
{ add_le_add_left       := assume a b h c, @add_le_add_left ℚ a b _ _ _ h c,
  lt_of_add_lt_add_left := assume a b c, @lt_of_add_lt_add_left ℚ a b c _ _ _,
  le_iff_exists_add     := assume ⟨a, ha⟩ ⟨b, hb⟩,
    iff.intro
      (assume h : a ≤ b,
        ⟨⟨b - a, le_sub_iff_add_le.2 $ by simp [h]⟩,
          nnrat.eq $ show b = a + (b - a), by rw [add_sub_cancel'_right]⟩)
      (assume ⟨⟨c, hc⟩, eq⟩, eq.symm ▸ show a ≤ a + c, from (le_add_iff_nonneg_right a).2 hc),
  ..nnrat.comm_semiring,
  ..nnrat.order_bot,
  ..nnrat.linear_order }

instance : distrib_lattice ℚ≥0 := by apply_instance

instance : semilattice_inf_bot ℚ≥0 :=
{ .. nnrat.order_bot, .. nnrat.distrib_lattice }

instance : semilattice_sup_bot ℚ≥0 :=
{ .. nnrat.order_bot, .. nnrat.distrib_lattice }

instance : linear_ordered_semiring ℚ≥0 :=
{ add_left_cancel            := assume a b c h, nnrat.eq $
    @add_left_cancel ℚ _ a b c (nnrat.eq_iff.2 h),
  le_of_add_le_add_left      := assume a b c, @le_of_add_le_add_left ℚ _ _ _ a b c,
  mul_lt_mul_of_pos_left     := assume a b c, @mul_lt_mul_of_pos_left ℚ _ a b c,
  mul_lt_mul_of_pos_right    := assume a b c, @mul_lt_mul_of_pos_right ℚ _ a b c,
  zero_le_one                := @zero_le_one ℚ _,
  exists_pair_ne             := ⟨0, 1, ne_of_lt (@zero_lt_one ℚ _ _)⟩,
  .. nnrat.canonically_linear_ordered_add_monoid,
  .. nnrat.comm_semiring, }

instance : linear_ordered_comm_group_with_zero ℚ≥0 :=
{ mul_le_mul_left := assume a b h c, mul_le_mul (le_refl c) h (zero_le a) (zero_le c),
  zero_le_one := zero_le 1,
  .. nnrat.linear_ordered_semiring,
  .. nnrat.comm_group_with_zero }

instance : canonically_ordered_comm_semiring ℚ≥0 :=
{ .. nnrat.canonically_linear_ordered_add_monoid,
  .. nnrat.comm_semiring,
  .. (show no_zero_divisors ℚ≥0, by apply_instance),
  .. nnrat.comm_group_with_zero }

instance : densely_ordered ℚ≥0 :=
⟨assume a b (h : (a : ℚ) < b), let ⟨c, hac, hcb⟩ := exists_between h in
  ⟨⟨c, le_trans a.property $ le_of_lt $ hac⟩, hac, hcb⟩⟩

instance : no_top_order ℚ≥0 :=
⟨assume a, let ⟨b, hb⟩ := no_top (a:ℚ) in ⟨⟨b, le_trans a.property $ le_of_lt $ hb⟩, hb⟩⟩

lemma bdd_above_coe {s : set ℚ≥0} : bdd_above ((coe : ℚ≥0 → ℚ) '' s) ↔ bdd_above s :=
iff.intro
  (assume ⟨b, hb⟩, ⟨nnrat.of_rat b, assume ⟨y, hy⟩ hys, show y ≤ max b 0, from
    le_max_left_of_le $ hb $ set.mem_image_of_mem _ hys⟩)
  (assume ⟨b, hb⟩, ⟨b, assume y ⟨x, hx, eq⟩, eq ▸ hb hx⟩)

lemma bdd_below_coe (s : set ℚ≥0) : bdd_below ((coe : ℚ≥0 → ℚ) '' s) :=
⟨0, assume r ⟨q, _, eq⟩, eq ▸ q.2⟩

instance : archimedean ℚ≥0 :=
⟨ assume x y pos_y,
  let ⟨n, hr⟩ := archimedean.arch (x:ℚ) (pos_y : (0 : ℚ) < y) in
  ⟨n, show (x:ℚ) ≤ (n • y : ℚ≥0), by simp [*, -nsmul_eq_mul, nsmul_coe]⟩ ⟩

lemma le_of_forall_pos_le_add {a b : ℚ≥0} (h : ∀ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
le_of_forall_le_of_dense $ assume x hxb,
begin
  rcases le_iff_exists_add.1 (le_of_lt hxb) with ⟨ε, rfl⟩,
  exact h _ ((lt_add_iff_pos_right b).1 hxb)
end

-- TODO: generalize to some ordered add_monoids, based on #6145
lemma le_of_add_le_left {a b c : ℚ≥0} (h : a + b ≤ c) : a ≤ c :=
by { refine le_trans _ h, simp }

lemma le_of_add_le_right {a b c : ℚ≥0} (h : a + b ≤ c) : b ≤ c :=
by { refine le_trans _ h, simp }

lemma bot_eq_zero : (⊥ : ℚ≥0) = 0 := rfl

lemma mul_sup (a b c : ℚ≥0) : a * (b ⊔ c) = (a * b) ⊔ (a * c) :=
begin
  cases le_total b c with h h,
  { simp [sup_eq_max, max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h (zero_le a))] },
  { simp [sup_eq_max, max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h (zero_le a))] },
end

lemma mul_finset_sup {α} {f : α → ℚ≥0} {s : finset α} (r : ℚ≥0) :
  r * s.sup f = s.sup (λa, r * f a) :=
begin
  refine s.induction_on _ _,
  { simp [bot_eq_zero] },
  { assume a s has ih, simp [has, ih, mul_sup], }
end

@[simp, norm_cast] lemma coe_max (x y : ℚ≥0) :
  ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
by { delta max, split_ifs; refl }

@[simp, norm_cast] lemma coe_min (x y : ℚ≥0) :
  ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
by { delta min, split_ifs; refl }

section of_rat

@[simp] lemma zero_le_coe {q : ℚ≥0} : 0 ≤ (q : ℚ) := q.2

@[simp] lemma of_rat_zero : nnrat.of_rat 0 = 0 :=
by simp [nnrat.of_rat]; refl

@[simp] lemma of_rat_one : nnrat.of_rat 1 = 1 :=
by simp [nnrat.of_rat, max_eq_left (zero_le_one : (0 :ℚ) ≤ 1)]; refl

@[simp] lemma of_rat_pos {r : ℚ} : 0 < nnrat.of_rat r ↔ 0 < r :=
by simp [nnrat.of_rat, nnrat.coe_lt_coe.symm, lt_irrefl]

@[simp] lemma of_rat_eq_zero {r : ℚ} : nnrat.of_rat r = 0 ↔ r ≤ 0 :=
by simpa [-of_rat_pos] using (not_iff_not.2 (@of_rat_pos r))

lemma of_rat_of_nonpos {r : ℚ} : r ≤ 0 → nnrat.of_rat r = 0 :=
of_rat_eq_zero.2

@[simp] lemma of_rat_le_of_rat_iff {r p : ℚ} (hp : 0 ≤ p) :
  nnrat.of_rat r ≤ nnrat.of_rat p ↔ r ≤ p :=
by simp [nnrat.coe_le_coe.symm, nnrat.of_rat, hp]

@[simp] lemma of_rat_lt_of_rat_iff' {r p : ℚ} :
  nnrat.of_rat r < nnrat.of_rat p ↔ r < p ∧ 0 < p :=
by simp [nnrat.coe_lt_coe.symm, nnrat.of_rat, lt_irrefl]

lemma of_rat_lt_of_rat_iff {r p : ℚ} (h : 0 < p) :
  nnrat.of_rat r < nnrat.of_rat p ↔ r < p :=
of_rat_lt_of_rat_iff'.trans (and_iff_left h)

lemma of_rat_lt_of_rat_iff_of_nonneg {r p : ℚ} (hr : 0 ≤ r) :
  nnrat.of_rat r < nnrat.of_rat p ↔ r < p :=
of_rat_lt_of_rat_iff'.trans ⟨and.left, λ h, ⟨h, lt_of_le_of_lt hr h⟩⟩

@[simp] lemma of_rat_add {r p : ℚ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
  nnrat.of_rat (r + p) = nnrat.of_rat r + nnrat.of_rat p :=
nnrat.eq $ by simp [nnrat.of_rat, hr, hp, add_nonneg]

lemma of_rat_add_of_rat {r p : ℚ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
  nnrat.of_rat r + nnrat.of_rat p = nnrat.of_rat (r + p) :=
(of_rat_add hr hp).symm

lemma of_rat_le_of_rat {r p : ℚ} (h : r ≤ p) : nnrat.of_rat r ≤ nnrat.of_rat p :=
nnrat.of_rat_mono h

lemma of_rat_add_le {r p : ℚ} : nnrat.of_rat (r + p) ≤ nnrat.of_rat r + nnrat.of_rat p :=
nnrat.coe_le_coe.1 $ max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) nnrat.zero_le_coe

lemma of_rat_le_iff_le_coe {r : ℚ} {p : ℚ≥0} : nnrat.of_rat r ≤ p ↔ r ≤ ↑p :=
nnrat.gi.gc r p

lemma le_of_rat_iff_coe_le {r : ℚ≥0} {p : ℚ} (hp : 0 ≤ p) : r ≤ nnrat.of_rat p ↔ ↑r ≤ p :=
by rw [← nnrat.coe_le_coe, nnrat.coe_of_rat p hp]

lemma le_of_rat_iff_coe_le' {r : ℚ≥0} {p : ℚ} (hr : 0 < r) : r ≤ nnrat.of_rat p ↔ ↑r ≤ p :=
(le_or_lt 0 p).elim le_of_rat_iff_coe_le $ λ hp,
  by simp only [(hp.trans_le r.coe_nonneg).not_le, of_rat_eq_zero.2 hp.le, hr.not_le]

lemma of_rat_lt_iff_lt_coe {r : ℚ} {p : ℚ≥0} (ha : 0 ≤ r) : nnrat.of_rat r < p ↔ r < ↑p :=
by rw [← nnrat.coe_lt_coe, nnrat.coe_of_rat r ha]

lemma lt_of_rat_iff_coe_lt {r : ℚ≥0} {p : ℚ} : r < nnrat.of_rat p ↔ ↑r < p :=
begin
  cases le_total 0 p,
  { rw [← nnrat.coe_lt_coe, nnrat.coe_of_rat p h] },
  { rw [of_rat_eq_zero.2 h], split,
    intro, have := not_lt_of_le (zero_le r), contradiction,
    intro rp, have : ¬(p ≤ 0) := not_le_of_lt (lt_of_le_of_lt (coe_nonneg _) rp), contradiction }
end

@[simp] lemma of_rat_bit0 {r : ℚ} (hr : 0 ≤ r) :
  nnrat.of_rat (bit0 r) = bit0 (nnrat.of_rat r) :=
of_rat_add hr hr

@[simp] lemma of_rat_bit1 {r : ℚ} (hr : 0 ≤ r) :
  nnrat.of_rat (bit1 r) = bit1 (nnrat.of_rat r) :=
(of_rat_add (by simp [hr]) zero_le_one).trans (by simp [of_rat_one, bit1, hr])

end of_rat

section mul

lemma mul_eq_mul_left {a b c : ℚ≥0} (h : a ≠ 0) : (a * b = a * c ↔ b = c) :=
begin
  rw [← nnrat.eq_iff, ← nnrat.eq_iff, nnrat.coe_mul, nnrat.coe_mul], split,
  { exact mul_left_cancel' (mt (@nnrat.eq_iff a 0).1 h) },
  { assume h, rw [h] }
end

lemma of_rat_mul {p q : ℚ} (hp : 0 ≤ p) :
  nnrat.of_rat (p * q) = nnrat.of_rat p * nnrat.of_rat q :=
begin
  cases le_total 0 q with hq hq,
  { apply nnrat.eq,
    simp [nnrat.of_rat, hp, hq, max_eq_left, mul_nonneg] },
  { have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq,
    rw [of_rat_eq_zero.2 hq, of_rat_eq_zero.2 hpq, mul_zero] }
end

end mul

section sub

lemma sub_def {r p : ℚ≥0} : r - p = nnrat.of_rat (r - p) := rfl

lemma sub_eq_zero {r p : ℚ≥0} (h : r ≤ p) : r - p = 0 :=
nnrat.eq $ max_eq_right $ sub_le_iff_le_add.2 $ by simpa [nnrat.coe_le_coe] using h

@[simp] lemma sub_self {r : ℚ≥0} : r - r = 0 := sub_eq_zero $ le_refl r

@[simp] lemma sub_zero {r : ℚ≥0} : r - 0 = r :=
by rw [sub_def, nnrat.coe_zero, sub_zero, nnrat.of_rat_coe]

lemma sub_pos {r p : ℚ≥0} : 0 < r - p ↔ p < r :=
of_rat_pos.trans $ sub_pos.trans $ nnrat.coe_lt_coe

protected lemma sub_lt_self {r p : ℚ≥0} : 0 < r → 0 < p → r - p < r :=
assume hr hp,
begin
  cases le_total r p,
  { rwa [sub_eq_zero h] },
  { rw [← nnrat.coe_lt_coe, nnrat.coe_sub h], exact sub_lt_self _ hp }
end

@[simp] lemma sub_le_iff_le_add {r p q : ℚ≥0} : r - p ≤ q ↔ r ≤ q + p :=
match le_total p r with
| or.inl h := by rw [← nnrat.coe_le_coe, ← nnrat.coe_le_coe, nnrat.coe_sub h, nnrat.coe_add,
    sub_le_iff_le_add]
| or.inr h :=
  have r ≤ p + q, from le_add_right h,
  by simpa [nnrat.coe_le_coe, nnrat.coe_le_coe, sub_eq_zero h, add_comm]
end

@[simp] lemma sub_le_self {r p : ℚ≥0} : r - p ≤ r :=
sub_le_iff_le_add.2 $ le_add_right $ le_refl r

lemma add_sub_cancel {r p : ℚ≥0} : (p + r) - r = p :=
nnrat.eq $ by rw [nnrat.coe_sub, nnrat.coe_add, add_sub_cancel]; exact le_add_left (le_refl _)

lemma add_sub_cancel' {r p : ℚ≥0} : (r + p) - r = p :=
by rw [add_comm, add_sub_cancel]

lemma sub_add_eq_max {r p : ℚ≥0} : (r - p) + p = max r p :=
nnrat.eq $ by rw [sub_def, nnrat.coe_add, coe_max, nnrat.of_rat, coe_mk,
  ← max_add_add_right, zero_add, sub_add_cancel]

lemma add_sub_eq_max {r p : ℚ≥0} : p + (r - p) = max p r :=
by rw [add_comm, sub_add_eq_max, max_comm]

@[simp] lemma sub_add_cancel_of_le {a b : ℚ≥0} (h : b ≤ a) : (a - b) + b = a :=
by rw [sub_add_eq_max, max_eq_left h]

lemma sub_sub_cancel_of_le {r p : ℚ≥0} (h : r ≤ p) : p - (p - r) = r :=
by rw [nnrat.sub_def, nnrat.sub_def, nnrat.coe_of_rat _ $ sub_nonneg.2 h,
  sub_sub_cancel, nnrat.of_rat_coe]

lemma lt_sub_iff_add_lt {p q r : ℚ≥0} : p < q - r ↔ p + r < q :=
begin
  split,
  { assume H,
    have : (((q - r) : ℚ≥0) : ℚ) = (q : ℚ) - (r : ℚ) :=
      nnrat.coe_sub (le_of_lt (sub_pos.1 (lt_of_le_of_lt (zero_le _) H))),
    rwa [← nnrat.coe_lt_coe, this, lt_sub_iff_add_lt, ← nnrat.coe_add] at H },
  { assume H,
    have : r ≤ q := le_trans (le_add_left (le_refl _)) (le_of_lt H),
    rwa [← nnrat.coe_lt_coe, nnrat.coe_sub this, lt_sub_iff_add_lt, ← nnrat.coe_add] }
end

lemma sub_lt_iff_lt_add {a b c : ℚ≥0} (h : b ≤ a) : a - b < c ↔ a < b + c :=
by simp only [←nnrat.coe_lt_coe, nnrat.coe_sub h, nnrat.coe_add, sub_lt_iff_lt_add']

lemma sub_eq_iff_eq_add {a b c : ℚ≥0} (h : b ≤ a) : a - b = c ↔ a = c + b :=
by rw [←nnrat.eq_iff, nnrat.coe_sub h, ←nnrat.eq_iff, nnrat.coe_add, sub_eq_iff_eq_add]

end sub

section inv

lemma sum_div {ι} (s : finset ι) (f : ι → ℚ≥0) (b : ℚ≥0) :
  (∑ i in s, f i) / b = ∑ i in s, (f i / b) :=
by simp only [div_eq_mul_inv, finset.sum_mul]

@[simp] lemma inv_pos {r : ℚ≥0} : 0 < r⁻¹ ↔ 0 < r :=
by simp [pos_iff_ne_zero]

lemma div_pos {r p : ℚ≥0} (hr : 0 < r) (hp : 0 < p) : 0 < r / p :=
by simpa only [div_eq_mul_inv] using mul_pos hr (inv_pos.2 hp)

protected lemma mul_inv {r p : ℚ≥0} : (r * p)⁻¹ = p⁻¹ * r⁻¹ := nnrat.eq $ mul_inv_rev' _ _

lemma div_self_le (r : ℚ≥0) : r / r ≤ 1 :=
if h : r = 0 then by simp [h] else by rw [div_self h]

@[simp] lemma inv_le {r p : ℚ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p :=
by rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]

lemma inv_le_of_le_mul {r p : ℚ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p :=
by by_cases r = 0; simp [*, inv_le]

@[simp] lemma le_inv_iff_mul_le {r p : ℚ≥0} (h : p ≠ 0) : (r ≤ p⁻¹ ↔ r * p ≤ 1) :=
by rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

@[simp] lemma lt_inv_iff_mul_lt {r p : ℚ≥0} (h : p ≠ 0) : (r < p⁻¹ ↔ r * p < 1) :=
by rw [← mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

lemma mul_le_iff_le_inv {a b r : ℚ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
have 0 < r, from lt_of_le_of_ne (zero_le r) hr.symm,
by rw [← @mul_le_mul_left _ _ a _ r this, ← mul_assoc, mul_inv_cancel hr, one_mul]

lemma le_div_iff_mul_le {a b r : ℚ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
by rw [div_eq_inv_mul, ← mul_le_iff_le_inv hr, mul_comm]

lemma div_le_iff {a b r : ℚ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r :=
@div_le_iff ℚ _ a r b $ pos_iff_ne_zero.2 hr

lemma lt_div_iff {a b r : ℚ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
lt_iff_lt_of_le_iff_le (div_le_iff hr)

lemma mul_lt_of_lt_div {a b r : ℚ≥0} (h : a < b / r) : a * r < b :=
begin
  refine (lt_div_iff $ λ hr, false.elim _).1 h,
  subst r,
  simpa using h
end

lemma le_of_forall_lt_one_mul_le {x y : ℚ≥0} (h : ∀a<1, a * x ≤ y) : x ≤ y :=
le_of_forall_ge_of_dense $ assume a ha,
  have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha),
  have hx' : x⁻¹ ≠ 0, by rwa [(≠), inv_eq_zero],
  have a * x⁻¹ < 1, by rwa [← lt_inv_iff_mul_lt hx', inv_inv'],
  have (a * x⁻¹) * x ≤ y, from h _ this,
  by rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this

lemma div_add_div_same (a b c : ℚ≥0) : a / c + b / c = (a + b) / c :=
eq.symm $ right_distrib a b (c⁻¹)

lemma half_pos {a : ℚ≥0} (h : 0 < a) : 0 < a / 2 := div_pos h zero_lt_two

lemma add_halves (a : ℚ≥0) : a / 2 + a / 2 = a := nnrat.eq (add_halves a)

lemma half_lt_self {a : ℚ≥0} (h : a ≠ 0) : a / 2 < a :=
by rw [← nnrat.coe_lt_coe, nnrat.coe_div]; exact
half_lt_self (bot_lt_iff_ne_bot.2 h)

lemma two_inv_lt_one : (2⁻¹:ℚ≥0) < 1 :=
by simpa using half_lt_self zero_ne_one.symm

lemma div_lt_iff {a b c : ℚ≥0} (hc : c ≠ 0) : b / c < a ↔ b < a * c :=
lt_iff_lt_of_le_iff_le $ nnrat.le_div_iff_mul_le hc

lemma div_lt_one_of_lt {a b : ℚ≥0} (h : a < b) : a / b < 1 :=
begin
  rwa [div_lt_iff, one_mul],
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)
end

@[field_simps] lemma div_add_div (a : ℚ≥0) {b : ℚ≥0} (c : ℚ≥0) {d : ℚ≥0}
  (hb : b ≠ 0) (hd : d ≠ 0) : a / b + c / d = (a * d + b * c) / (b * d) :=
begin
  rw ← nnrat.eq_iff,
  simp only [nnrat.coe_add, nnrat.coe_div, nnrat.coe_mul],
  exact div_add_div _ _ (coe_ne_zero.2 hb) (coe_ne_zero.2 hd)
end

@[field_simps] lemma add_div' (a b c : ℚ≥0) (hc : c ≠ 0) :
  b + a / c = (b * c + a) / c :=
by simpa using div_add_div b a one_ne_zero hc

@[field_simps] lemma div_add' (a b c : ℚ≥0) (hc : c ≠ 0) :
  a / c + b = (a + b * c) / c :=
by rwa [add_comm, add_div', add_comm]

lemma of_rat_inv {x : ℚ} :
  nnrat.of_rat x⁻¹ = (nnrat.of_rat x)⁻¹ :=
begin
  by_cases hx : 0 ≤ x,
  { nth_rewrite 0 ← coe_of_rat x hx,
    rw [←nnrat.coe_inv, of_rat_coe], },
  { have hx' := le_of_not_ge hx,
    rw [of_rat_eq_zero.mpr hx', inv_zero, of_rat_eq_zero.mpr (inv_nonpos.mpr hx')], },
end

lemma of_rat_div {x y : ℚ} (hx : 0 ≤ x) :
  nnrat.of_rat (x / y) = nnrat.of_rat x / nnrat.of_rat y :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ←of_rat_inv, ←of_rat_mul hx]

lemma of_rat_div' {x y : ℚ} (hy : 0 ≤ y) :
  nnrat.of_rat (x / y) = nnrat.of_rat x / nnrat.of_rat y :=
by rw [div_eq_inv_mul, div_eq_inv_mul, of_rat_mul (inv_nonneg.2 hy), of_rat_inv]

end inv

@[simp] lemma abs_eq (x : ℚ≥0) : abs (x : ℚ) = x :=
abs_of_nonneg x.property

end nnrat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot] def rational.nnabs (x : ℚ) : ℚ≥0 := ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp] lemma nnrat.coe_nnabs (x : ℚ) : (rational.nnabs x : ℚ) = abs x :=
by simp [rational.nnabs]
