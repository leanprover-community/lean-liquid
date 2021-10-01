import topology.continuous_function.algebra
import analysis.normed_space.basic
import ring_theory.finiteness
import linear_algebra.free_module.finite

import for_mathlib.nnrat
import for_mathlib.rational_cones

/-

# Gordan's Lemma

-/

universe u
variables {Λ : Type u} [add_comm_group Λ]
variable {ι : Type*}

open_locale big_operators
open_locale nnreal

def explicit_dual_set (l : ι → Λ) : submodule ℕ (Λ →+ ℤ) :=
{ carrier := {x | ∀ i, 0 ≤ x (l i)},
  zero_mem' := λ i, le_rfl,
  add_mem' := λ x y hx hy i, add_nonneg (hx i) (hy i),
  smul_mem' := λ n x hx i, nsmul_nonneg (hx i) n }

lemma mem_explicit_dual_set (l : ι → Λ) (x : Λ →+ ℤ) :
  x ∈ explicit_dual_set l ↔ ∀ i, 0 ≤ x (l i) := iff.rfl

def dual_finset (S : finset Λ) : submodule ℕ (Λ →+ ℤ) :=
explicit_dual_set (coe : (S : set Λ) → Λ)

lemma mem_dual_finset (S : finset Λ) (l : Λ →+ ℤ) :
  l ∈ dual_finset S ↔ ∀ x ∈ S, 0 ≤ l x :=
begin
  rw [dual_finset, mem_explicit_dual_set],
  simp
end

lemma dual_finset_antimono {S T : finset Λ} (hST : S ⊆ T) :
  dual_finset T ≤ dual_finset S :=
begin
  rintro φ hφ ⟨i, his : i ∈ S⟩,
  exact hφ ⟨i, hST his⟩,
end

lemma explicit_dual_set_eq_dual_finset [decidable_eq Λ] [fintype ι] (l : ι → Λ) :
  explicit_dual_set l = dual_finset (finset.image l finset.univ) :=
begin
  ext φ,
  split,
  { rintro hφ ⟨t, ht : t ∈ finset.image _ _⟩,
    rw finset.mem_image at ht,
    rcases ht with ⟨i, -, rfl⟩,
    exact hφ i },
  { rintro hφ i,
    refine hφ ⟨l i, (_ : l i ∈ finset.image _ _)⟩,
    rw finset.mem_image,
    exact ⟨i, finset.mem_univ _, rfl⟩ }
end

def intersect_halfspaces (l : ι → Λ →+ ℤ) : submodule ℕ Λ :=
{ carrier := {x | ∀ i, 0 ≤ l i x},
  zero_mem' := λ i, by simp only [add_monoid_hom.map_zero],
  add_mem' := λ x y hx hy i,
  begin
    simp only [add_monoid_hom.map_add],
    apply add_nonneg (hx i) (hy i)
  end,
  smul_mem' := λ c x hx i,
  begin
    simp only [nsmul_eq_mul, int.nat_cast_eq_coe_nat, add_monoid_hom.map_nsmul],
    apply mul_nonneg (int.coe_zero_le c) (hx i),
  end }

lemma mem_intersect_halfspaces (l : ι → Λ →+ ℤ) (x : Λ) :
  x ∈ intersect_halfspaces l ↔ ∀ i, 0 ≤ l i x := iff.rfl

def intersect_halfspaces_set (s : set (Λ →+ ℤ)) : submodule ℕ Λ :=
intersect_halfspaces (coe : (s : set (Λ →+ ℤ)) → (Λ →+ ℤ))

lemma mem_intersect_halfspaces_set (S : set (Λ →+ ℤ)) (x : Λ) :
  x ∈ intersect_halfspaces_set S ↔ ∀ (f : Λ →+ ℤ), f ∈ S → 0 ≤ f x :=
begin
  rw [intersect_halfspaces_set, mem_intersect_halfspaces],
  simp
end

variables {α : Type*}

def to_rational_point : (α → ℤ) →ₗ[ℤ] (α → ℚ) :=
{ to_fun := λ f x, f x,
  map_add' := λ f g,
  begin
    ext x,
    simp,
  end,
  map_smul' := λ m f,
  begin
    ext x,
    simp,
  end }

@[simp] lemma to_rational_point_apply (x : α → ℤ) (i : α) :
  to_rational_point x i = x i := rfl

lemma to_rational_point_injective : function.injective (to_rational_point : (α → ℤ) → (α → ℚ)) :=
begin
  intros x y h,
  ext i,
  rw function.funext_iff at h,
  specialize h i,
  simpa using h
end

def lattice_restrict (S : submodule (ℚ≥0) (α → ℚ)) :
  submodule ℕ (α → ℤ) :=
{ carrier := to_rational_point ⁻¹' (S : set (α → ℚ)),
  zero_mem' :=
    by simp only [linear_map.map_zero, set.mem_preimage, set_like.mem_coe, submodule.zero_mem],
  add_mem' := λ a b (ha : to_rational_point a ∈ S) (hb : to_rational_point b ∈ S),
  begin
    change to_rational_point (a + b) ∈ S,
    simp only [linear_map.map_add],
    apply S.add_mem ha hb,
  end,
  smul_mem' := λ c x (hx : to_rational_point x ∈ S),
  begin
    change to_rational_point (c • x) ∈ S,
    rw linear_map.map_smul_of_tower,
    exact submodule.smul_of_tower_mem S c hx,
  end }

lemma mem_lattice_restrict (S : submodule (ℚ≥0) (α → ℚ)) (x : α → ℤ) :
  x ∈ lattice_restrict S ↔ to_rational_point x ∈ S :=
iff.rfl

def is_integer (x : ℚ) := ∃ (z : ℤ), x = z
def is_integer_point (x : α → ℚ) := ∀ a, is_integer (x a)

def floor_point (x : α → ℚ) : α → ℤ := λ i, ⌊x i⌋
lemma floor_point_eq_of_is_integer_point (x : α → ℚ) (hx : is_integer_point x) :
  (λ i, floor_point x i : α → ℚ) = x :=
begin
  ext i,
  obtain ⟨z, hz⟩ := hx i,
  simp [floor_point, hz],
end

lemma exists_scalings {ι : Type*} (s : finset ι) (v : ι → ℚ) :
  ∃ (n : ℕ), 0 < n ∧ ∀ i ∈ s, is_integer (n • v i) :=
begin
  classical,
  apply finset.induction_on s,
  { exact ⟨1, by norm_num, by simp⟩ },
  { rintro x s hx ⟨m, hm₁, hm₂⟩,
    refine ⟨m * (v x).denom, mul_pos hm₁ (v x).pos, _⟩,
    simp only [forall_eq_or_imp, nsmul_eq_mul, finset.mem_insert, nat.cast_mul],
    refine ⟨⟨m * (v x).num, _⟩, _⟩,
    { push_cast,
      rw mul_assoc,
      norm_cast,
      rw [mul_comm ((v x).denom : ℚ), rat.mul_denom_eq_num],
      norm_cast },
    intros y hy,
    obtain ⟨z, hz⟩ := hm₂ y hy,
    rw mul_right_comm,
    refine ⟨z * (v x).denom, _⟩,
    push_cast,
    rw ←hz,
    simp }
end

lemma point_exists_scaling {α : Type*} [fintype α] (x : α → ℚ) :
  ∃ (n : ℕ), 0 < n ∧ is_integer_point ((n) • x) :=
let ⟨m, hm₁, hm₂⟩ := exists_scalings finset.univ x in ⟨m, hm₁, λ a, by simpa using hm₂ a⟩

open_locale classical

noncomputable def scale_factor {α : Type*} [fintype α] (x : α → ℚ) : ℕ :=
nat.find (point_exists_scaling x)

lemma scale_factor_pos {α : Type*} [fintype α] (x : α → ℚ) : 0 < scale_factor x :=
(nat.find_spec (point_exists_scaling x)).1

lemma rat_scale_factor_ne_zero {α : Type*} [fintype α] (x : α → ℚ) :
  (scale_factor x : ℚ) ≠ 0 :=
begin
  norm_cast,
  apply (scale_factor_pos x).ne',
end

noncomputable def scale_up {α : Type*} [fintype α] (x : α → ℚ) : α → ℤ :=
floor_point (scale_factor x • x)

lemma scale_up_is {α : Type*} [fintype α] (x : α → ℚ) :
  (λ (i : α), ↑(scale_up x i)) = scale_factor x • x :=
floor_point_eq_of_is_integer_point _ (nat.find_spec (point_exists_scaling x)).2

lemma scale_up_coord {α : Type*} [fintype α] (x : α → ℚ) (a : α) :
  (scale_up x a : ℚ) = scale_factor x * x a :=
begin
  suffices : (scale_up x a : ℚ) = (scale_factor x • x) a,
  { simpa using this },
  rw ←scale_up_is,
end

lemma to_rational_point_scale_up {α : Type*} [fintype α] (x : α → ℚ) :
  to_rational_point (scale_up x) = scale_factor x • x :=
begin
  ext i,
  simp [scale_up_coord],
end

example {a b : ℤ} : (a : ℚ) = b → a = b :=
λ h, (rat.coe_int_inj a b).mp h

noncomputable def upgrade_functional {α : Type*} [fintype α] (f : (α → ℤ) →+ ℤ) : (α → ℚ) →ₗ[ℚ] ℚ :=
{ to_fun := λ g, (f (scale_up g) : ℚ) / scale_factor g,
  map_add' := λ g₁ g₂,
  begin
    field_simp [rat_scale_factor_ne_zero],
    norm_cast,
    suffices : f ((scale_factor g₁ * scale_factor g₂) • scale_up (g₁ + g₂)) =
      f (scale_factor (g₁ + g₂) • (scale_factor g₂ • scale_up g₁ + scale_factor g₁ • scale_up g₂)),
    { simp only [add_monoid_hom.map_nsmul, add_monoid_hom.map_add] at this,
      simp only [nsmul_eq_mul, int.nat_cast_eq_coe_nat, mul_comm _ (f _)] at this,
      rw this,
      apply mul_comm },
    congr' 1,
    ext a,
    simp only [pi.add_apply, pi.smul_apply],
    simp only [nsmul_eq_mul, int.nat_cast_eq_coe_nat, int.coe_nat_mul, mul_add],
    rw ←rat.coe_int_inj,
    push_cast,
    simp only [scale_up_coord, pi.add_apply],
    ring!,
  end,
  map_smul' := λ m x,
  begin
    simp only [algebra.id.smul_eq_mul],
    rw ←rat.num_div_denom m,
    field_simp [rat_scale_factor_ne_zero, m.pos.ne', -rat.num_div_denom],
    simp only [rat.num_div_denom],
    norm_cast,
    suffices :
      f ((m.denom * scale_factor x) • scale_up (m • x)) =
        f ((scale_factor (m • x) * m.num : ℤ) • scale_up x),
    { simp only [add_monoid_hom.map_gsmul, add_monoid_hom.map_nsmul] at this,
      simp only [int.coe_nat_mul],
      simp only [algebra.id.smul_eq_mul, rat.num_div_denom, nsmul_eq_mul, int.nat_cast_eq_coe_nat,
        int.coe_nat_mul] at this,
      rw [mul_comm (f _), this, mul_comm _ m.num, mul_right_comm] },
    congr' 1,
    ext a,
    simp only [pi.smul_apply],
    simp only [algebra.id.smul_eq_mul, nsmul_eq_mul, int.nat_cast_eq_coe_nat, int.coe_nat_mul],
    rw ←rat.coe_int_inj,
    push_cast,
    simp only [scale_up_coord, pi.smul_apply, algebra.id.smul_eq_mul, ←rat.mul_denom_eq_num],
    ring!,
  end }.

lemma thingy {R : Type*} [semiring R] (t : ℕ) (a : α) : (t : R) = (coe t : α → R) a :=
begin
  simp only [pi.coe_nat],
  -- simp only [int.nat_cast_eq_coe_nat, pi.coe_nat],
end

lemma thingy' (t : ℕ) (a : α) : (t : ℤ) = (coe t : α → ℤ) a :=
begin
  simp only [int.nat_cast_eq_coe_nat, pi.coe_nat],
end

lemma upgrade_id {α : Type*} [fintype α] (f : (α → ℤ) →+ ℤ) (g : α → ℤ) :
  upgrade_functional f (to_rational_point g) = f g :=
begin
  dsimp [upgrade_functional, to_rational_point],
  rw div_eq_iff (rat_scale_factor_ne_zero _),
  norm_cast,
  rw [mul_comm, ←int.nat_cast_eq_coe_nat, ←nsmul_eq_mul, ←add_monoid_hom.map_nsmul],
  congr' 1,
  ext a,
  simp only [nsmul_eq_mul, pi.mul_apply],
  rw ←rat.coe_int_inj,
  rw scale_up_coord,
  norm_cast,
  congr' 1,
  apply thingy',
end

section

lemma finitely_generated_iff_integrally_generated [fintype α] (C : submodule (ℚ≥0) (α → ℚ)) :
  C.fg ↔ ∃ S : finset (α → ℤ), submodule.span (ℚ≥0) (S.image to_rational_point : set (α → ℚ)) = C :=
begin
  split,
  { rintro ⟨S, rfl⟩,
    refine ⟨S.image scale_up, _⟩,
    apply le_antisymm,
    { rw submodule.span_le,
      intros x,
      simp only [to_rational_point_scale_up, and_imp, set.mem_image, finset.mem_coe,
        exists_exists_and_eq_and, set_like.mem_coe, exists_imp_distrib, finset.coe_image],
      rintro y hy rfl,
      have : y ∈ submodule.span (ℚ≥0) (S : set (α → ℚ)) := submodule.subset_span hy,
      have z := submodule.smul_mem _ (scale_factor y : ℚ≥0) this,
      convert z using 1,
      ext i,
      simp only [nsmul_eq_mul, pi.smul_apply],
      change _ = _ * _,
      congr' 1,
      simp },
    { rw submodule.span_le,
      intros x,
      simp only [set_like.mem_coe, finset.mem_coe, finset.coe_image, ←set.image_comp],
      intro hx,
      have : scale_factor x • x ∈ ((to_rational_point ∘ scale_up) '' (S : set (α → ℚ))),
      { refine ⟨_, hx, _⟩,
        simp only [nsmul_eq_mul, function.comp_app, to_rational_point_scale_up] },
      have : scale_factor x • x ∈
        submodule.span ℚ≥0 (to_rational_point ∘ scale_up '' (S : set (α → ℚ))) :=
        submodule.subset_span this,
      have hx₂ := submodule.smul_mem _ ((scale_factor x)⁻¹ : ℚ≥0) this,
      convert hx₂ using 1,
      ext i,
      simp only [nsmul_eq_mul, pi.mul_apply, pi.smul_apply],
      change _ = _ * (_ * _),
      simp,
      rw ←mul_assoc,
      convert (one_mul (x i)).symm,
      convert inv_mul_cancel _,
      apply (thingy _ _).symm,
      apply rat_scale_factor_ne_zero } },
  { rintro ⟨S, rfl⟩,
    refine ⟨_, rfl⟩ }
end.

lemma finitely_generated_iff_integrally_generated_type {α : Type u} [fintype α]
  (C : submodule (ℚ≥0) (α → ℚ)) :
  C.fg ↔ ∃ (ι : Type u) (s : finset ι) (v : ι → α → ℤ) (hv : function.injective v),
    submodule.span (ℚ≥0) (s.image (λ i, to_rational_point (v i)) : set (α → ℚ)) = C :=
begin
  rw finitely_generated_iff_integrally_generated,
  split,
  { rintro ⟨S, rfl⟩,
    refine ⟨_, S, id, λ _ _ h, h, rfl⟩ },
  { rintro ⟨ι, s, v, _, rfl⟩,
    refine ⟨s.image v, _⟩,
    rw finset.image_image }
end

lemma bounded_lattice_thing [fintype α] {k : α → ℕ} (C : set (α → ℤ))
  (hC : ∀ (x : α → ℤ) i, x ∈ C → int.nat_abs (x i) ≤ k i) : C.finite :=
begin
  classical,
  let C' : finset (α → ℤ) :=
    (finset.univ.pi (λ i, finset.Ico_ℤ (-k i) (k i+1))).image (λ f a, f a (finset.mem_univ _)),
  have : C ⊆ C',
  { intros x hx,
    simp only [set.mem_image, finset.mem_univ, finset.mem_pi, forall_true_left, finset.mem_coe,
      finset.Ico_ℤ.mem, finset.coe_image],
    refine ⟨λ a _, x a, λ a _, _, _⟩,
    { simp only [finset.Ico_ℤ.mem],
      have : abs (x a) ≤ k a,
      { rw int.abs_eq_nat_abs,
        exact_mod_cast hC x a hx },
      rw abs_le at this,
      refine ⟨this.1, _⟩,
      rw int.lt_add_one_iff,
      apply this.2 },
    refl },
  apply set.finite.subset _ this,
  exact finset.finite_to_set C',
end

lemma finset.sum_nat_abs_le {ι : Type*} (s : finset ι) (f : ι → ℤ) :
  (∑ i in s, f i).nat_abs ≤ ∑ i in s, (f i).nat_abs :=
finset.le_sum_of_subadditive _ rfl int.nat_abs_add_le _ _

lemma floor_add_floor_le {α : Type*} [linear_ordered_ring α] [floor_ring α] (x y : α) :
  ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ :=
begin
  rw [le_floor, int.cast_add],
  apply add_le_add (floor_le x) (floor_le y),
end

lemma finset.floor_le {α : Type*} [linear_ordered_ring α] [floor_ring α] {ι : Type*} (s : finset ι)
  (f : ι → α) :
  ∑ i in s, ⌊f i⌋ ≤ ⌊∑ i in s, f i⌋ :=
begin
  apply finset.induction_on s,
  { simp },
  { intros i s hi ih,
    rw [finset.sum_insert hi, finset.sum_insert hi],
    apply le_trans (add_le_add_left ih _) (floor_add_floor_le _ _) }
end

lemma ceil_add_le {α : Type*} [linear_ordered_ring α] [floor_ring α] (x y : α) :
  ⌈x + y⌉ ≤ ⌈x⌉ + ⌈y⌉ :=
begin
  rw [ceil_le, int.cast_add],
  apply add_le_add (le_ceil x) (le_ceil y),
end

lemma finset.le_ceil {α : Type*} [linear_ordered_ring α] [floor_ring α] {ι : Type*} (s : finset ι)
  (f : ι → α) :
  ⌈∑ i in s, f i⌉ ≤ ∑ i in s, ⌈f i⌉ :=
finset.le_sum_of_subadditive _ (by simp) ceil_add_le _ _

lemma nat_abs_lt_nat_abs_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) :
  a.nat_abs < b.nat_abs :=
begin
  lift b to ℕ using le_trans w₁ (le_of_lt w₂),
  lift a to ℕ using w₁,
  simpa using w₂,
end

lemma int.coe_sum {α : Type*} (f : α → ℕ) (s : finset α) :
  ∑ (x : α) in s, (f x : ℤ) = (↑∑ i in s, f i : ℤ) :=
begin
  apply finset.induction_on s,
  { simp },
  { intros i t hi ih,
    simp only [finset.sum_insert hi, ih],
    simp }
end

lemma finset.mem_span_iff {R M : Type*} [ring R] [add_comm_monoid M] [module R M] (S : finset M)
  (x : M) :
  x ∈ submodule.span R (S : set M) ↔ ∃ (w : M → R), ∑ i in S, w i • i = x :=
begin
  exact mem_span_finset
end

set_option pp.proofs true

lemma missing [fintype α] (w : α → ℤ) (n : ℕ) :
  to_rational_point (n • w) = (n : ℚ≥0) • to_rational_point w :=
begin
  simp only [nsmul_eq_mul],
  induction n,
  { simp },
  { simp [add_smul, ←n_ih, add_mul],  },
end

lemma my_result [fintype α] (C : submodule (ℚ≥0) (α → ℚ)) (hC : C.fg) :
  (lattice_restrict C).fg :=
begin
  rw finitely_generated_iff_integrally_generated_type at hC,
  rcases hC with ⟨ι, s, w, hw, rfl⟩,
  let B := {x : α → ℤ |
                ∃ w' : ι → ℚ≥0, (∀ (i ∈ s), w' i < 1) ∧
                ∑ i in s, w' i • to_rational_point (w i) = to_rational_point x},
  let k : α → ℕ := λ a, ∑ i in s, int.nat_abs (w i a),
  have : ∀ (x : α → ℤ) a, x ∈ B → int.nat_abs (x a) ≤ k a,
  { rintro x a ⟨w', hw', hw''⟩,
    have hw''' : (∑ (i : ι) in s, w' i • to_rational_point (w i)) a = to_rational_point x a,
    { rw hw'' },
    simp only [finset.sum_apply, algebra.id.smul_eq_mul, to_rational_point_apply,
      pi.smul_apply] at hw''',
    change ∑ (c : ι) in s, (w' c : ℚ) * (w c a) = x a at hw''',
    clear hw'',
    have : abs (∑ (c : ι) in s, (w' c : ℚ) * w c a) ≤ ∑ (c : ι) in s, abs (w c a),
    { apply le_trans (finset.abs_sum_le_sum_abs _ _) _,
      apply finset.sum_le_sum,
      intros i hi,
      rw abs_mul,
      apply mul_le_of_le_one_left,
      exact abs_nonneg (w i a),
      rw abs_le,
      refine ⟨_, (hw' i hi).le⟩,
      apply le_trans (show (-1 : ℚ) ≤ 0, by norm_num) (w' i).2 },
    rw hw''' at this,
    norm_cast at this,
    simp only [int.abs_eq_nat_abs] at this,
    rw int.coe_sum at this,
    norm_cast at this,
    apply this },
  let B' := set.finite.to_finset (bounded_lattice_thing _ this),
  refine ⟨B' ∪ s.image w, _⟩,
  apply le_antisymm,
  { rw submodule.span_le,
    simp only [set.union_subset_iff, finset.coe_union, set.finite.coe_to_finset],
    split,
    { rintro x ⟨w', hw', hw''⟩,
      change to_rational_point x ∈ _,
      rw ←hw'',
      simp only [set_like.mem_coe],
      refine submodule.sum_smul_mem _ _ _,
      intros i hi,
      apply submodule.subset_span,
      simp only [set.mem_image, finset.mem_coe, finset.coe_image],
      refine ⟨_, hi, rfl⟩ },
    { simp only [set.image_subset_iff, finset.coe_image],
      intros x hx,
      change to_rational_point (w x) ∈ _,
      apply submodule.subset_span,
      refine ⟨_, hx, rfl⟩ } },
  { rintro x (hx : to_rational_point _ ∈ _),
    simp only [set_like.mem_coe, mem_span_finset] at hx,
    rcases hx with ⟨f, hf⟩,
    rw finset.sum_image at hf,
    { simp only [finset.coe_union, set.finite.coe_to_finset, finset.coe_image],
      let f' : ι → ℚ≥0 := λ i, f (to_rational_point (w i)),
      let ns : ι → ℕ := λ i, (⌊(f' i : ℚ)⌋).nat_abs,
      let g' : ι → ℚ≥0 := λ i, f' i - ns i,
      have ns' : ∀ i, (ns i : ℤ) = ⌊(f' i : ℚ)⌋,
      { intro i,
        change (int.nat_abs _ : ℤ) = _,
        rw [←int.abs_eq_nat_abs, abs_of_nonneg],
        rw [floor_nonneg],
        apply (f' i).2 },
      have hg' : ∀ i, (g' i : ℚ) = f' i - ns i,
      { intros i,
        change max _ _ = _,
        simp only [nnrat.coe_nat_cast],
        rw max_eq_left,
        rw sub_nonneg,
        change (int.nat_abs _ : ℚ) ≤ _,
        suffices : ((int.nat_abs ⌊(f' i : ℚ)⌋ : ℤ) : ℚ) ≤ f' i,
        { simpa using this },
        rw ns',
        apply floor_le },
      change ∑ x in s, f' x • to_rational_point (w x) = to_rational_point x at hf,
      -- have :  ≤ ↑(f' i) - ↑(ns i)
      have : ∀ i, (ns i : ℚ≥0) + g' i = f' i,
      { intro i,
        apply nnrat.coe_injective,
        rw [nnrat.coe_add, hg'],
        simp },
      simp_rw [←this, add_smul, finset.sum_add_distrib] at hf,
      let x_floors := ∑ (x : ι) in s, ns x • w x,
      have : x - x_floors ∈ B,
      { refine ⟨g', _, _⟩,
        { intros i hi,
          rw ←nnrat.coe_lt_coe,
          rw hg',
          simp only [nnrat.coe_one],
          suffices : (f' i : ℚ) - ((ns i : ℤ) : ℚ) < 1,
          { simpa using this },
          rw ns',
          apply fract_lt_one },
        rw linear_map.map_sub,
        rw linear_map.map_sum,
        rw eq_sub_iff_add_eq',
        rw ←hf,
        congr' 1,
        apply finset.sum_congr rfl,
        intros i hi,
        apply missing },
      { have : x = x - x_floors + x_floors,
        { simp },
        rw this,
        refine submodule.add_mem _ _ _,
        { apply submodule.subset_span,
          left,
          apply ‹x - x_floors ∈ B› },
        apply submodule.sum_smul_mem _ ns _,
        intros i hi,
        apply submodule.subset_span,
        right,
        refine ⟨_, hi, rfl⟩ } },
    intros x hx y hy t,
    apply hw,
    apply to_rational_point_injective t, }
end

end

instance {α : Type*} [fintype α] : finite_dimensional ℚ (α → ℚ) :=
@is_noetherian_pi _ _ _ _ _ _ _ (λ i, infer_instance)

lemma finset_Gordan_aux_pi {α : Type*} [fintype α] (S : finset ((α → ℤ) →+ ℤ)) :
  (intersect_halfspaces_set (S : set ((α → ℤ) →+ ℤ))).fg  :=
begin
  classical,
  let S' : finset ((α → ℚ) →ₗ[ℚ] ℚ) := S.image upgrade_functional,
  suffices : lattice_restrict (set_down_one (S' : set ((α → ℚ) →ₗ[ℚ] ℚ))) =
              intersect_halfspaces_set (S : set ((α → ℤ) →+ ℤ)),
  { rw ←this,
    apply my_result,
    rw ←fg_iff_is_polyhedral_cone,
    rw is_polyhedral_cone_iff_finset,
    refine ⟨_, rfl⟩ },
  ext x,
  simp [mem_lattice_restrict, mem_intersect_halfspaces_set, upgrade_id],
end

/-- A finset version of Gordan's Lemma. -/
lemma finset_Gordan_aux [module.finite ℤ Λ] [module.free ℤ Λ] (S : finset (Λ →+ ℤ)) :
  (intersect_halfspaces_set (S : set (Λ →+ ℤ))).fg :=
begin
  classical,
  have e := linear_equiv.restrict_scalars ℕ (module.free.choose_basis ℤ Λ).equiv_fun,
    -- deliberately forget the data here, it makes the simp at the end easier
  let e' : (Λ →+ ℤ) → (module.free.choose_basis_index ℤ Λ → ℤ) →+ ℤ :=
    λ f, f.comp e.symm.to_linear_map.to_add_monoid_hom,
  let L := (intersect_halfspaces_set ↑(S.image e')).map
    (e.symm : (module.free.choose_basis_index ℤ Λ → ℤ) →ₗ[ℕ] Λ),
  have : L.fg := submodule.fg_map (finset_Gordan_aux_pi (S.image e')),
  suffices : L = intersect_halfspaces_set (S : set (Λ →+ ℤ)),
  { rwa ←this },
  ext x,
  simp [mem_intersect_halfspaces_set, linear_equiv.symm_apply_eq],
end

/-- A finset version of Gordan's Lemma. -/
lemma finset_Gordan [module.finite ℤ Λ] [module.free ℤ Λ] (S : finset Λ) :
  (dual_finset S).fg :=
begin
  classical,
  let S' : finset ((Λ →+ ℤ) →+ ℤ) := S.image add_monoid_hom.eval,
  have := finset_Gordan_aux S',
  convert this using 1,
  ext x,
  simp [mem_dual_finset, mem_intersect_halfspaces_set],
end

/-- A fintype version of Gordan's Lemma. -/
lemma explicit_gordan [module.finite ℤ Λ] [module.free ℤ Λ] [fintype ι] (l : ι → Λ) :
  (explicit_dual_set l).fg :=
begin
  classical,
  rw explicit_dual_set_eq_dual_finset,
  apply finset_Gordan,
end
