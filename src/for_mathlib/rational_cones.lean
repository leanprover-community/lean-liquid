import linear_algebra.dual
import linear_algebra.free_module.basic

import for_mathlib.nnrat

universe u
variables {Λ : Type u} [add_comm_group Λ]
variable {ι : Type*}

open_locale big_operators
open_locale nnreal

variable {α : Type*}

def nnrat_module {Λ : Type*} [add_comm_group Λ] [module ℚ Λ] : module (ℚ≥0) Λ :=
restrict_scalars.module (ℚ≥0) ℚ Λ

local attribute [instance] nnrat_module

instance nnrat_tower [module ℚ Λ] : is_scalar_tower (ℚ≥0) ℚ Λ :=
{ smul_assoc := λ x y z,
  begin
    rcases x with ⟨x, hx⟩,
    change (x • y) • z = x • _,
    simp [mul_smul],
  end }

variable [module ℚ Λ]
open module

def index_up_one (l : ι → Λ) : submodule (ℚ≥0) (dual ℚ Λ) :=
{ carrier := {x | ∀ i, 0 ≤ x (l i)},
  zero_mem' := λ i, le_rfl,
  add_mem' := λ x y hx hy i, by simpa only [linear_map.add_apply] using add_nonneg (hx _) (hy _),
  smul_mem' := λ c x hx i, mul_nonneg c.2 (hx i) }

@[simp] lemma mem_index_up_one (l : ι → Λ) (x : dual ℚ Λ) :
  x ∈ index_up_one l ↔ ∀ i, 0 ≤ x (l i) :=
iff.rfl

def set_up_one (s : set Λ) : submodule (ℚ≥0) (dual ℚ Λ) :=
index_up_one (coe : s → Λ)

lemma set_up_one_def (s : set Λ) : set_up_one s = index_up_one (coe : s → Λ) := rfl

lemma index_up_one_eq_set_up_one_range (l : ι → Λ) :
  index_up_one l = set_up_one (set.range l) :=
begin
  ext φ,
  split,
  { rintro hφ ⟨_, i, rfl⟩,
    apply hφ i },
  { rintro hφ i,
    apply hφ ⟨_, i, rfl⟩ },
end

@[simp] lemma mem_set_up_one (s : set Λ) (x : dual ℚ Λ) :
  x ∈ set_up_one s ↔ ∀ i ∈ s, 0 ≤ x i :=
begin
  change x ∈ index_up_one _ ↔ _,
  simp,
end

lemma set_up_one_antitone (s t : set Λ) :
  s ≤ t → set_up_one t ≤ set_up_one s :=
begin
  rintro h f hf ⟨i, hi⟩,
  apply hf ⟨_, h hi⟩,
end

/-- The submodule given by the intersection of the given functionals -/
def index_down_one (l : ι → Λ →ₗ[ℚ] ℚ) : submodule (ℚ≥0) Λ :=
{ carrier := {x | ∀ i, 0 ≤ l i x},
  zero_mem' := λ i, by simp only [linear_map.map_zero],
  add_mem' := λ x y hx hy i, by simpa only [linear_map.map_add] using add_nonneg (hx i) (hy i),
  smul_mem' := λ c x (hx : ∀ i, 0 ≤ l i x) i,
  begin
    rw linear_map.map_smul_of_tower,
    apply mul_nonneg c.2 (hx i),
  end }

@[simp] lemma mem_index_down_one (l : ι → dual ℚ Λ) (x : Λ) :
  x ∈ index_down_one l ↔ ∀ i, 0 ≤ l i x :=
iff.rfl

def set_down_one (s : set (dual ℚ Λ)) : submodule (ℚ≥0) Λ :=
index_down_one (coe : s → dual ℚ Λ)

lemma set_down_one_def (s : set (dual ℚ Λ)) :
  set_down_one s = index_down_one (coe : s → dual ℚ Λ) := rfl

lemma index_down_one_eq_set_down_one_range (l : ι → dual ℚ Λ) :
  index_down_one l = set_down_one (set.range l) :=
begin
  ext φ,
  split,
  { rintro hφ ⟨_, i, rfl⟩,
    apply hφ i },
  { rintro hφ i,
    apply hφ ⟨_, i, rfl⟩ },
end

@[simp] lemma mem_set_down_one (s : set (dual ℚ Λ)) (x : Λ) :
  x ∈ set_down_one s ↔ ∀ (i : dual ℚ Λ), i ∈ s → 0 ≤ i x :=
begin
  change x ∈ index_down_one _ ↔ _,
  simp,
end

lemma set_down_one_antitone (s t : set (dual ℚ Λ)) :
  s ≤ t → set_down_one t ≤ set_down_one s :=
begin
  rintro h f hf ⟨i, hi⟩,
  apply hf ⟨_, h hi⟩,
end

lemma set_up_one_span (s : set Λ) :
  set_up_one (submodule.span (ℚ≥0) s : set Λ) = set_up_one s :=
begin
  ext f,
  simp only [mem_set_up_one, set_like.mem_coe],
  split,
  { intros t y hy,
    apply t _ (submodule.subset_span hy) },
  { intros hf y hy,
    apply submodule.span_induction hy hf (by simp),
    { intros l₁ l₂ hl₁ hl₂,
      simp only [linear_map.map_add],
      apply add_nonneg hl₁ hl₂ },
    { intros q y hy,
      simp only [linear_map.map_smul_of_tower],
      apply mul_nonneg q.2 hy } }
end

lemma set_down_one_span (s : set (dual ℚ Λ)) :
  set_down_one (submodule.span (ℚ≥0) s : set (dual ℚ Λ)) = set_down_one s :=
begin
  ext x,
  simp only [mem_set_down_one, set_like.mem_coe],
  split,
  { intros t y hy,
    apply t _ (submodule.subset_span hy) },
  { intros hx y hy,
    apply submodule.span_induction hy hx (by simp),
    { intros l₁ l₂ hl₁ hl₂,
      apply add_nonneg hl₁ hl₂ },
    { intros q f hf,
      simp only [linear_map.smul_apply],
      apply mul_nonneg q.2 hf } }
end

lemma le_up_down (l : set (dual ℚ Λ)) : l ≤ set_up_one (set_down_one l : set Λ) :=
begin
  rintro x hx ⟨i, hi⟩,
  apply hi ⟨_, hx⟩,
end

lemma le_down_up (l : set Λ) : l ≤ set_down_one (set_up_one l : set (dual ℚ Λ)) :=
begin
  rintro x hx ⟨i, hi⟩,
  apply hi ⟨_, hx⟩,
end

noncomputable def down_two [finite_dimensional ℚ Λ] :
  submodule (ℚ≥0) (dual ℚ (dual ℚ Λ)) → submodule (ℚ≥0) Λ :=
submodule.comap (linear_equiv.restrict_scalars (ℚ≥0) (eval_equiv ℚ Λ) : Λ →ₗ[ℚ≥0] dual ℚ (dual ℚ Λ))

lemma down_two_def [finite_dimensional ℚ Λ] (C : submodule (ℚ≥0) (dual ℚ (dual ℚ Λ))) :
  down_two C =
  C.comap (linear_equiv.restrict_scalars (ℚ≥0) (eval_equiv ℚ Λ) : Λ →ₗ[ℚ≥0] dual ℚ (dual ℚ Λ)) :=
rfl

noncomputable def up_two [finite_dimensional ℚ Λ] :
  submodule (ℚ≥0) Λ → submodule (ℚ≥0) (dual ℚ (dual ℚ Λ)) :=
submodule.map (linear_equiv.restrict_scalars (ℚ≥0) (eval_equiv ℚ Λ) : Λ →ₗ[ℚ≥0] dual ℚ (dual ℚ Λ))

lemma down_two_up [finite_dimensional ℚ Λ] (C : submodule (ℚ≥0) Λ) :
  down_two (up_two C) = C :=
begin
  dunfold up_two down_two,
  rw linear_equiv.map_eq_comap,
  rw ←submodule.comap_comp,
  simp only [linear_equiv.refl_to_linear_map, linear_equiv.self_trans_symm, linear_equiv.comp_coe,
    submodule.comap_id],
end

lemma up_two_down [finite_dimensional ℚ Λ] (C : submodule (ℚ≥0) (dual ℚ (dual ℚ Λ))) :
  up_two (down_two C) = C :=
begin
  dunfold up_two down_two,
  rw linear_equiv.map_eq_comap,
  rw ←submodule.comap_comp,
  simp [submodule.comap_id],
end

lemma down_two_index_up_one [finite_dimensional ℚ Λ] (l : ι → dual ℚ Λ) :
  down_two (index_up_one l) = index_down_one l :=
begin
  ext x,
  simp only [down_two, submodule.mem_comap, linear_equiv.coe_coe,
    linear_equiv.restrict_scalars_apply, mem_index_up_one, mem_index_down_one],
  refl
end

lemma down_two_set_up_one [finite_dimensional ℚ Λ] (l : set (dual ℚ Λ)) :
  down_two (set_up_one l) = set_down_one l :=
down_two_index_up_one _

lemma up_two_index_down_one [finite_dimensional ℚ Λ] (l : ι → dual ℚ Λ) :
  up_two (index_down_one l) = index_up_one l :=
begin
  rw ←down_two_index_up_one,
  simp only [up_two_down],
end

lemma up_two_set_down_one [finite_dimensional ℚ Λ] (l : set (dual ℚ Λ)) :
  up_two (set_down_one l) = set_up_one l :=
up_two_index_down_one _

lemma down_up_down_eq (l : set (dual ℚ Λ)) :
  set_down_one (set_up_one (set_down_one l : set Λ) : set (dual ℚ Λ)) = set_down_one l :=
begin
  apply le_antisymm,
  { apply set_down_one_antitone,
    apply le_up_down },
  { apply le_down_up }
end

lemma up_down_up_eq (l : set Λ) :
  set_up_one (set_down_one (set_up_one l : set (dual ℚ Λ)) : set Λ) = set_up_one l :=
begin
  apply le_antisymm,
  { apply set_up_one_antitone,
    apply le_down_up },
  { apply le_up_down }
end

lemma down_two_up_one_up_one [finite_dimensional ℚ Λ]
  (C : submodule (ℚ≥0) Λ) (hC : ∃ (l : set (dual ℚ Λ)), C = set_down_one l) :
  down_two (set_up_one (set_up_one (C : set Λ) : set (dual ℚ Λ))) = C :=
begin
  rw down_two_set_up_one,
  rcases hC with ⟨l, rfl⟩,
  rw down_up_down_eq
end

lemma down_eval_eq [finite_dimensional ℚ Λ] (C : set Λ) :
  set_down_one (eval_equiv ℚ Λ '' C) = set_up_one C :=
begin
  ext x,
  simp only [and_imp, set.mem_image, mem_set_down_one, mem_set_up_one, forall_apply_eq_imp_iff₂,
    exists_imp_distrib],
  refl
end

lemma down_one_up_two [finite_dimensional ℚ Λ] (C : submodule (ℚ≥0) Λ) :
  set_down_one (up_two C : set (dual ℚ (dual ℚ Λ))) = set_up_one C :=
down_eval_eq _

lemma up_one_down_two [finite_dimensional ℚ Λ] (C : submodule (ℚ≥0) (dual ℚ (dual ℚ Λ))) :
  set_up_one (down_two C : set Λ) = set_down_one C :=
begin
  simp only [←down_one_up_two],
  simp only [up_two_down],
end

lemma up_one_down_one [finite_dimensional ℚ Λ] (C : set (dual ℚ Λ)) :
  set_up_one (set_down_one C : set Λ) = set_down_one (set_up_one C) :=
begin
  rw ←down_two_set_up_one,
  simp only [up_one_down_two],
end

/-- A submodule is polyhedral if it is the intersection of finitely many half spaces. -/
def is_polyhedral_cone (C : submodule (ℚ≥0) Λ) : Prop :=
  ∃ (ι : Type u) (_ : fintype ι) (l : ι → Λ →ₗ[ℚ] ℚ), C = index_down_one l

lemma is_polyhedral_cone_iff_finset (C : submodule (ℚ≥0) Λ) :
  is_polyhedral_cone C ↔ ∃ (s : finset (dual ℚ Λ)), C = set_down_one s :=
begin
  classical,
  split,
  { rintro ⟨ι, hι, l, rfl⟩,
    resetI,
    refine ⟨finset.univ.image l, _⟩,
    rw index_down_one_eq_set_down_one_range l,
    simp },
  { rintro ⟨s, rfl⟩,
    exact ⟨(s : set (dual ℚ Λ)), infer_instance, _, set_down_one_def _⟩ }
end

lemma down_two_up_one_up_one_cone [finite_dimensional ℚ Λ]
  (C : submodule (ℚ≥0) Λ) (hC : is_polyhedral_cone C) :
  down_two (set_up_one (set_up_one (C : set Λ) : set (dual ℚ Λ))) = C :=
begin
  apply down_two_up_one_up_one,
  rw is_polyhedral_cone_iff_finset at hC,
  rcases hC with ⟨_, rfl⟩,
  refine ⟨_, rfl⟩,
end

lemma is_polyhedral_cone_of_equiv {Λ' : Type u} [add_comm_group Λ'] [module ℚ Λ']
  (e : Λ ≃ₗ[ℚ] Λ') (C : submodule (ℚ≥0) Λ) (hC : is_polyhedral_cone C) :
  is_polyhedral_cone (submodule.map (e.to_linear_map.restrict_scalars (ℚ≥0)) C) :=
begin
  rcases hC with ⟨ι, hι, l, rfl⟩,
  refine ⟨ι, hι, λ i, _, _⟩,
  apply (l i).comp e.symm.to_linear_map,
  ext x,
  simp only [submodule.mem_map, function.comp_app, linear_map.coe_comp,
    mem_index_down_one, linear_equiv.coe_to_linear_map,
    linear_map.coe_restrict_scalars_eq_coe],
  split,
  { rintro ⟨y, hy, rfl⟩,
    simpa },
  { intro t,
    refine ⟨e.symm x, t, by simp⟩ }
end

lemma is_polyhedral_cone_bot_aux [fintype α] : is_polyhedral_cone (⊥ : submodule (ℚ≥0) (α → ℚ)) :=
⟨α ⊕ α, sum.fintype α α,
    sum.elim (λ i, ⟨λ f, f i, λ x y, rfl, λ _ _, rfl⟩)
             (λ i, -⟨λ f, f i, λ x y, rfl, λ _ _, rfl⟩),
begin
  ext,
  simp only [linear_map.coe_proj, sum.elim_inl, function.eval_apply, linear_map.neg_apply,
    sum.elim_inr, mem_index_down_one, sum.forall, submodule.mem_bot, neg_nonneg],
  split,
  { rintro rfl,
    simp only [linear_map.map_zero, and_self],
    intro a,
    apply le_rfl },
  { rintro ⟨h₁, h₂⟩,
    ext1 i,
    apply le_antisymm,
    { apply h₂ i },
    { apply h₁ i } }
end⟩

lemma is_polyhedral_cone_bot [finite_dimensional ℚ Λ] :
  is_polyhedral_cone (⊥ : submodule (ℚ≥0) Λ) :=
begin
  let l := (basis.of_vector_space ℚ Λ).equiv_fun,
  have := is_polyhedral_cone_of_equiv l.symm ⊥ is_polyhedral_cone_bot_aux,
  simpa using this,
end

lemma coe_min' (s : finset (ℚ≥0)) (hs : s.nonempty) :
  (coe (s.min' hs) : ℚ) = (s.image coe).min' (hs.image _) :=
begin
  revert hs,
  apply finset.induction_on s,
  { simp },
  { intros x s hx ih t,
    rcases finset.eq_empty_or_nonempty s with (rfl | hs),
    { simp },
    simp_rw [finset.image_insert, finset.min'_insert x s hs, nnrat.coe_min, ih hs,
      ← finset.min'_insert] }
end

def extended_half_spaces_index {ι : Type*} (s : ι → Λ →ₗ[ℚ] ℚ) (x : Λ) : Type* :=
{i : ι // 0 ≤ s i x} ⊕ ({i : ι // 0 < s i x} × {i : ι // s i x < 0})

instance {ι : Type*} [fintype ι] (s : ι → Λ →ₗ[ℚ] ℚ) (x : Λ) :
  fintype (extended_half_spaces_index s x) :=
begin
  rw extended_half_spaces_index,
  apply_instance
end

def extended_half_spaces {ι : Type*} (s : ι → Λ →ₗ[ℚ] ℚ) (x : Λ) :
  extended_half_spaces_index s x → Λ →ₗ[ℚ] ℚ :=
sum.elim (s ∘ coe) (λ ij, (s ij.1 x) • s ij.2 - (s ij.2 x) • s ij.1)

lemma span_le_extended [decidable_eq Λ] {ι : Type*} {s : ι → Λ →ₗ[ℚ] ℚ}
  {l : finset Λ} (hs : submodule.span ℚ≥0 (l : set Λ) = index_down_one s)
  {x : Λ} (hx : x ∉ l) :
  submodule.span ℚ≥0 ↑(insert x l) ≤ index_down_one (extended_half_spaces s x) :=
begin
  rw submodule.span_le,
  intros f hf,
  simp only [finset.coe_insert, set.mem_insert_iff, finset.mem_coe] at hf,
  simp only [set_like.mem_coe, mem_index_down_one, extended_half_spaces],
  rcases hf with (rfl | hf),
  { rintro (⟨i, hi⟩ | ⟨⟨i, hi⟩, j, hj⟩),
    { simpa },
    { simp [mul_comm] } },
  { have f_mem : f ∈ index_down_one s,
    { rw ←hs,
      exact submodule.subset_span hf },
    rintro (⟨i, hi⟩ | ⟨⟨i, hi⟩, j, hj⟩),
    { simpa using f_mem i },
    { have : 0 ≤ s i f, by apply f_mem,
      have : 0 ≤ s j f, by apply f_mem,
      simp only [algebra.id.smul_eq_mul, sub_nonneg, linear_map.smul_apply, sum.elim_inr,
        subtype.coe_mk, linear_map.sub_apply],
      nlinarith } },
end

lemma extended_le_span [decidable_eq Λ] {ι : Type*} [fintype ι] {s : ι → Λ →ₗ[ℚ] ℚ}
  {l : finset Λ} (hs : submodule.span ℚ≥0 (l : set Λ) = index_down_one s)
  {x : Λ} (hx : x ∉ l) :
  index_down_one (extended_half_spaces s x) ≤ submodule.span ℚ≥0 ↑(insert x l) :=
begin
  intros y hy,
  simp only [finset.coe_insert, submodule.mem_span_insert, exists_prop, hs],
  suffices : ∃ (t : ℚ≥0), y - t • x ∈ index_down_one s,
  { rcases this with ⟨a, ha⟩,
    refine ⟨a, _, ha, by simp⟩ },
  simp only [mem_index_down_one] at hy,
  have y_nonneg : ∀ i, 0 ≤ s i x → 0 ≤ s i y,
  { intros i hi,
    apply hy (sum.inl ⟨i, hi⟩) },
  have y_neg : ∀ i j, 0 < s i x → s j x < 0 → s j x * s i y ≤ s i x * s j y,
  { intros i j hi hj,
    simpa [extended_half_spaces] using hy (sum.inr ⟨⟨i, hi⟩, ⟨j, hj⟩⟩) },
  let a : {i // 0 < s i x} → ℚ≥0 := λ i, ⟨s i.1 y, y_nonneg _ i.2.le⟩ / ⟨s i.1 x, i.2.le⟩,
  let as : finset (ℚ≥0) := finset.univ.image a,
  let b : {i // s i x < 0} → ℚ := λ i, s i.1 y / s i.1 x,
  let bs : finset ℚ := finset.univ.image b,
  by_cases h : nonempty {i // 0 < s i x},
  { have : as.nonempty,
    { rwa [finset.nonempty.image_iff, finset.univ_nonempty_iff] },
    refine ⟨as.min' ‹as.nonempty›, _⟩,
    rw [mem_index_down_one],
    intros i,
    rw [linear_map.map_sub, sub_nonneg],
    simp only [linear_map.map_smul_of_tower, subtype.val_eq_coe],
    change (coe (_ : ℚ≥0)) * (s i x) ≤ s i y,
    rcases lt_trichotomy 0 (s i x) with (lt | eq | gt),
    { rw [coe_min', ←le_div_iff lt],
      apply finset.min'_le,
      simp only [finset.mem_univ, finset.mem_image, exists_prop],
      refine ⟨_, ⟨⟨i, lt⟩, ⟨⟩, rfl⟩, _⟩,
      simp },
    { rw [←eq, mul_zero],
      apply y_nonneg _ (eq.le) },
    { rw [coe_min', ←div_le_iff_of_neg gt],
      apply finset.le_min',
      simp only [and_imp, exists_prop, finset.mem_univ, bex_imp_distrib, finset.mem_image,
        exists_true_left, subtype.exists, exists_imp_distrib],
      rintro _ _ j hj ⟨⟨⟩, rfl⟩ rfl,
      simp only [nnrat.coe_div, subtype.coe_mk],
      have := y_neg _ _ hj gt,
      rwa [div_le_iff_of_neg gt, ←mul_div_right_comm, mul_comm, div_le_iff' hj] } },
  by_cases h' : nonempty {i // s i x < 0},
  { have : bs.nonempty,
    { rwa [finset.nonempty.image_iff, finset.univ_nonempty_iff] },
    refine ⟨nnrat.of_rat (bs.max' ‹bs.nonempty›), _⟩,
    intros i,
    rw [linear_map.map_sub, sub_nonneg],
    simp only [linear_map.map_smul_of_tower, subtype.val_eq_coe],
    rcases lt_trichotomy 0 (s i x) with (lt | eq | gt),
    { exfalso,
      apply h,
      refine ⟨⟨_, lt⟩⟩ },
    { rw [←eq, smul_zero],
      apply y_nonneg,
      apply eq.le, },
    change max _ _ * _ ≤ _,
    rw ←div_le_iff_of_neg gt,
    rw le_max_iff,
    left,
    apply finset.le_max',
    simp only [finset.mem_univ, finset.mem_image, exists_true_left, subtype.exists],
    refine ⟨i, gt, finset.mem_univ _, rfl⟩ },
  refine ⟨0, _⟩,
  intros i,
  rw [linear_map.map_sub, sub_nonneg, zero_smul, linear_map.map_zero],
  simp only [linear_map.map_smul_of_tower, subtype.val_eq_coe],
  rcases le_or_lt 0 (s i x) with (lt | lt),
  { apply y_nonneg _ lt },
  { exfalso,
    apply h',
    refine ⟨⟨_, lt⟩⟩ },
end

lemma eliminate_inductive_step [decidable_eq Λ] (ι : Type u) [fintype ι] (s : ι → Λ →ₗ[ℚ] ℚ)
  {l : finset Λ} (hs : submodule.span ℚ≥0 (l : set Λ) = index_down_one s)
  (x : Λ) (hx : x ∉ l) :
  is_polyhedral_cone (submodule.span ℚ≥0 (coe (insert x l) : set Λ)) :=
begin
  refine ⟨extended_half_spaces_index s x, infer_instance, extended_half_spaces _ _, _⟩,
  apply le_antisymm,
  apply span_le_extended hs hx,
  apply extended_le_span hs hx,
end

lemma elimination_aux [finite_dimensional ℚ Λ] (l : finset Λ) :
  is_polyhedral_cone (submodule.span (ℚ≥0) (l : set Λ)) :=
begin
  classical,
  apply finset.induction_on l,
  { simp only [finset.coe_empty, submodule.span_empty],
    apply is_polyhedral_cone_bot },
  { clear l,
    rintro x l hx ⟨ι, hι, s, hs⟩,
    resetI,
    convert eliminate_inductive_step ι s hs x hx }
end

lemma is_polyhedral_cone_of_fg [finite_dimensional ℚ Λ] (C : submodule (ℚ≥0) Λ) (hC : C.fg) :
  is_polyhedral_cone C :=
begin
  rcases hC with ⟨l, rfl⟩,
  apply elimination_aux
end

lemma one_sixteen_c [finite_dimensional ℚ Λ] (ι : Type u) [fintype ι] (l : ι → Λ →ₗ[ℚ] ℚ) :
  set_up_one (index_down_one l : set Λ) =
    submodule.span (ℚ≥0) (set.range l) :=
begin
  set C : submodule (ℚ≥0) Λ := index_down_one l,
  set C_star := set_up_one (C : set Λ),
  set C' : submodule _ (dual ℚ Λ) := submodule.span (ℚ≥0) (set.range l),
  let C'_star := down_two (set_up_one (C' : set (dual ℚ Λ))),
  have C_eq : C = C'_star,
  { change C = down_two (set_up_one (C' : set (dual ℚ Λ))),
    rw down_two_set_up_one,
    rw set_down_one_span,
    apply index_down_one_eq_set_down_one_range },
  have C'pc : is_polyhedral_cone C',
  { apply is_polyhedral_cone_of_fg,
    classical,
    refine ⟨finset.univ.image l, _⟩,
    simp },
  change set_up_one (C : set Λ) = _,
  rw C_eq,
  change set_up_one (down_two (set_up_one (C' : set (dual ℚ Λ))) : set Λ) = _,
  rw down_two_set_up_one,
  rw is_polyhedral_cone_iff_finset at C'pc,
  clear_value C', clear' C C_star C'_star C_eq l,
  rcases C'pc with ⟨s, rfl⟩,
  simp_rw [up_one_down_one (set_down_one (s : set (dual ℚ (dual ℚ Λ))) : set (dual ℚ Λ))],
  rw down_up_down_eq,
end

lemma dual_fg_of_cone [finite_dimensional ℚ Λ] (C : submodule (ℚ≥0) Λ)
  (hC : is_polyhedral_cone C) :
  (set_up_one (C : set Λ) : submodule (ℚ≥0) (dual ℚ Λ)).fg :=
begin
  rcases hC with ⟨ι, hι, l, rfl⟩,
  resetI,
  simp only [one_sixteen_c],
  classical,
  refine ⟨finset.univ.image l, by simp⟩,
end

lemma fg_of_is_polyhedral_cone [finite_dimensional ℚ Λ] (C : submodule (ℚ≥0) Λ)
  (hC : is_polyhedral_cone C) :
  C.fg :=
begin
  have t := dual_fg_of_cone _ (is_polyhedral_cone_of_fg _ (dual_fg_of_cone _ hC)),
  have t2 : (submodule.map
      (((eval_equiv ℚ Λ).restrict_scalars (ℚ≥0)).symm : dual ℚ (dual ℚ Λ) →ₗ[ℚ≥0] Λ) _).fg,
  { refine submodule.fg.map _ t, },
  rwa [linear_equiv.map_eq_comap, linear_equiv.symm_symm, ← down_two_def,
    down_two_up_one_up_one_cone _ hC] at t2,
end

lemma fg_iff_is_polyhedral_cone [finite_dimensional ℚ Λ] (C : submodule (ℚ≥0) Λ) :
  is_polyhedral_cone C ↔ C.fg :=
⟨fg_of_is_polyhedral_cone C, is_polyhedral_cone_of_fg C⟩
