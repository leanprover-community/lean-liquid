import pseudo_normed_group.profinitely_filtered
/-!

# Profinitely filtered pseudo-normed groups with T⁻¹

The definition of `profinitely_filtered_pseudo_normed_group_with_Tinv`,
and morphisms between them.

-/
open pseudo_normed_group profinitely_filtered_pseudo_normed_group
  comphaus_filtered_pseudo_normed_group
open_locale nnreal big_operators

local attribute [instance] type_pow

/-- A *profinitely filtered pseudo-normed topological group with action by `T⁻¹`* is
a profinitely filtered pseudo-normed topological group `M` together with a
nonnegative real `r'` and homomorphism `Tinv : M → M` such that
`Tinv x ∈ filtration M (r'⁻¹ * c)` for all `x ∈ filtration M c`.

Morphisms are continuous and strict homomorphisms. -/
class profinitely_filtered_pseudo_normed_group_with_Tinv (r' : out_param $ ℝ≥0) (M : Type*)
  extends profinitely_filtered_pseudo_normed_group M :=
(Tinv : comphaus_filtered_pseudo_normed_group_hom M M)
(Tinv_mem_filtration : ∀ c x, x ∈ filtration c → Tinv x ∈ filtration (r'⁻¹ * c))

namespace profinitely_filtered_pseudo_normed_group_with_Tinv

variables {r' : ℝ≥0} {M M₁ M₂ M₃ : Type*}
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₁]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₂]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₃]

lemma aux {r' c c₂ : ℝ≥0} (h : c ≤ r' * c₂) : r'⁻¹ * c ≤ c₂ :=
begin
  by_cases hr' : r' = 0,
  { subst r', rw [inv_zero, zero_mul], exact zero_le' },
  { rwa [nnreal.mul_le_iff_le_inv, inv_inv₀], exact inv_ne_zero hr' }
end

@[simps]
def Tinv₀ (c c₂ : ℝ≥0) [h : fact (c ≤ r' * c₂)] (x : filtration M c) : filtration M c₂ :=
⟨Tinv (x : M), filtration_mono (aux h.1) (Tinv_mem_filtration _ _ x.2)⟩

lemma Tinv₀_continuous (c c₂ : ℝ≥0) [fact (c ≤ r' * c₂)] :
  continuous (@Tinv₀ r' M _ c c₂ _) :=
Tinv.continuous _ $ λ x, rfl

lemma Tinv_bound_by : (@Tinv _ M _).bound_by (r'⁻¹) := Tinv_mem_filtration

end profinitely_filtered_pseudo_normed_group_with_Tinv

section
set_option old_structure_cmd true

open profinitely_filtered_pseudo_normed_group_with_Tinv

structure profinitely_filtered_pseudo_normed_group_with_Tinv_hom (r' : ℝ≥0) (M₁ M₂ : Type*)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₁]
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₂]
  extends M₁ →+ M₂ :=
(strict' : ∀ ⦃c x⦄, x ∈ filtration M₁ c → to_fun x ∈ filtration M₂ c)
(continuous' : ∀ c, continuous (pseudo_normed_group.level to_fun strict' c))
(map_Tinv' : ∀ x, to_fun (Tinv x) = Tinv (to_fun x))

end

attribute [nolint doc_blame] profinitely_filtered_pseudo_normed_group_with_Tinv_hom.mk
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom.to_add_monoid_hom

namespace profinitely_filtered_pseudo_normed_group_with_Tinv_hom

open profinitely_filtered_pseudo_normed_group_with_Tinv

variables {r' : ℝ≥0} {M M₁ M₂ M₃ : Type*}
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₁]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₂]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₃]
variables (f g : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂)

instance : has_coe_to_fun (profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂) :=
⟨_, profinitely_filtered_pseudo_normed_group_with_Tinv_hom.to_fun⟩

@[simp] lemma coe_mk (f) (h₁) (h₂) (h₃) (h₄) (h₅) :
  ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂) = f :=
rfl

@[simp] lemma mk_to_monoid_hom (f) (h₁) (h₂) (h₃) (h₄) (h₅) :
  (⟨f, h₁, h₂, h₃, h₄, h₅⟩ :
    profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂).to_add_monoid_hom =
    ⟨f, h₁, h₂⟩ := rfl

@[simp] lemma coe_to_add_monoid_hom : ⇑f.to_add_monoid_hom = f := rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sum {ι : Type*} (x : ι → M₁) (s : finset ι) :
  f (∑ i in s, x i) = ∑ i in s, f (x i) :=
f.to_add_monoid_hom.map_sum _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

@[simp] lemma map_gsmul (n : ℤ) (x) : f (n • x) = n • (f x) := f.to_add_monoid_hom.map_gsmul _ _

lemma strict : ∀ ⦃c x⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ c := f.strict'

/-- `f.level c` is the function `filtration M₁ c → filtration M₂ c`
induced by a `profinitely_filtered_pseudo_normed_group_with_Tinv_hom M₁ M₂`. -/
@[simps] def level : ∀ (c : ℝ≥0), filtration M₁ c → filtration M₂ c :=
pseudo_normed_group.level f f.strict

lemma level_continuous (c : ℝ≥0) : continuous (f.level c) := f.continuous' c

lemma map_Tinv (x : M₁) : f (Tinv x) = Tinv (f x) := f.map_Tinv' x

variables {f g}

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

instance : has_zero (profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂) :=
⟨{ strict' := λ c x h, zero_mem_filtration _,
   continuous' := λ c, @continuous_const _ (filtration M₂ c) _ _ 0,
   map_Tinv' := λ x, show 0 = Tinv (0 : M₂), from Tinv.map_zero.symm,
   .. (0 : M₁ →+ M₂) }⟩

instance : inhabited (profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂) := ⟨0⟩

lemma coe_inj ⦃f g : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂⦄
  (h : (f : M₁ → M₂) = g) :
  f = g :=
by cases f; cases g; cases h; refl

/-- The identity function as `profinitely_filtered_pseudo_normed_group_with_Tinv_hom`. -/
@[simps] def id : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M M :=
{ strict' := λ c x, id,
  continuous' := λ c, by { convert continuous_id, ext, refl },
  map_Tinv' := λ x, rfl,
  .. add_monoid_hom.id _ }

/-- The composition of `profinitely_filtered_pseudo_normed_group_with_Tinv_hom`s. -/
@[simps] def comp
  (g : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₂ M₃)
  (f : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂) :
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₃ :=
{ strict' := λ c x hx, g.strict (f.strict hx),
  continuous' := λ c, (g.level_continuous c).comp (f.level_continuous c),
  map_Tinv' := λ x,
  calc g (f (Tinv x)) = g (Tinv (f x)) : by rw f.map_Tinv
                  ... = Tinv (g (f x)) : by rw g.map_Tinv,
  .. (g.to_add_monoid_hom.comp f.to_add_monoid_hom) }

variables (f)

/-- The `profinitely_filtered_pseudo_normed_group_hom` underlying a
`profinitely_filtered_pseudo_normed_group_with_Tinv_hom`. -/
def to_profinitely_filtered_pseudo_normed_group_hom :
  comphaus_filtered_pseudo_normed_group_hom M₁ M₂ :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_strict f.to_add_monoid_hom
(λ c, ⟨λ x h, f.strict h, f.level_continuous c⟩)

lemma to_profinitely_filtered_pseudo_normed_group_hom_strict :
  f.to_profinitely_filtered_pseudo_normed_group_hom.strict :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_strict_strict _ _

variables {f}

def mk' (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂)
  (hf1 : f.bound_by 1) (hfT) :
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂ :=
{ to_fun := f,
  strict' := λ c x hx, by simpa only [one_mul] using hf1 hx,
  continuous' := λ c, f.continuous _ (λ x, rfl),
  map_Tinv' := hfT,
  .. f }

@[simp] lemma mk'_apply
  (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) (hf1) (hfT) (x : M₁) :
  @mk' r' _ _ _ _ f hf1 hfT x = f x := rfl

/-- If the inverse of `profinitely_filtered_pseudo_normed_group_with_Tinv_hom` is strict, then it
is a `profinitely_filtered_pseudo_normed_group_with_Tinv_hom`. -/
def inv_of_equiv_of_strict (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) :
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₂ M₁ :=
{ strict' := strict,
  continuous' := λ c,
  begin
    simp only [add_equiv.coe_to_add_monoid_hom, add_monoid_hom.to_fun_eq_coe],
    have hcont := f.continuous' c,
    let g : (filtration M₁ c) ≃ (filtration M₂ c) :=
    ⟨λ x, ⟨f x, f.strict x.2⟩, λ x, ⟨e.symm x, strict x.2⟩, λ x, by simp [he], λ x, by simp [he]⟩,
    change continuous g.symm,
    rw continuous_iff_is_closed,
    intros U hU,
    rw [← g.image_eq_preimage],
    exact (hcont.closed_embedding g.injective).is_closed_map U hU,
  end,
  map_Tinv' := λ x,
  begin
    apply e.injective,
    simp only [add_equiv.coe_to_add_monoid_hom, add_monoid_hom.to_fun_eq_coe],
    rw [e.apply_symm_apply, ← he, map_Tinv, he, e.apply_symm_apply],
  end,
  .. e.symm.to_add_monoid_hom }

@[simp]
lemma inv_of_equiv_of_strict.apply (x : M₁) (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) :
  (inv_of_equiv_of_strict e he strict) (f x) = x := by simp [inv_of_equiv_of_strict, he]

@[simp]
lemma inv_of_equiv_of_strict_symm.apply (x : M₂) (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) :
  f (inv_of_equiv_of_strict e he strict x) = x := by simp [inv_of_equiv_of_strict, he]

end profinitely_filtered_pseudo_normed_group_with_Tinv_hom

namespace punit

instance profinitely_filtered_pseudo_normed_group_with_Tinv (r' : ℝ≥0) :
  profinitely_filtered_pseudo_normed_group_with_Tinv r' punit :=
{ Tinv := comphaus_filtered_pseudo_normed_group_hom.id,
  Tinv_mem_filtration := λ c x h, set.mem_univ _,
  .. punit.profinitely_filtered_pseudo_normed_group }

end punit

namespace profinitely_filtered_pseudo_normed_group_with_Tinv

section
/-! ## Powers -/

noncomputable theory

variables (r' : ℝ≥0) {ι : Type*} (M M₁ M₂ : ι → Type*)
variables [Π i, profinitely_filtered_pseudo_normed_group_with_Tinv r' (M i)]
variables [Π i, profinitely_filtered_pseudo_normed_group_with_Tinv r' (M₁ i)]
variables [Π i, profinitely_filtered_pseudo_normed_group_with_Tinv r' (M₂ i)]

instance pi : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Π i, M i) :=
{ Tinv := comphaus_filtered_pseudo_normed_group.pi_map (λ i, Tinv)
    ⟨r'⁻¹, λ i, Tinv_bound_by⟩,
  Tinv_mem_filtration := λ c x hx i, Tinv_mem_filtration _ _ (hx i),
  .. profinitely_filtered_pseudo_normed_group.pi _ }

instance pi' (M : Type*) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] (N : ℕ) :
  profinitely_filtered_pseudo_normed_group_with_Tinv r' (M^N) :=
profinitely_filtered_pseudo_normed_group_with_Tinv.pi r' (λ i, M)

include r'
@[simp] lemma pi_Tinv_apply (x : Π i, M i) (i : ι) : Tinv x i = Tinv (x i) := rfl
omit r'

@[simps {fully_applied := ff}]
def pi_proj (i : ι) : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' (Π i, M i) (M i) :=
{ to_fun := pi.eval_add_monoid_hom M i,
  strict' := λ c x hx, hx i,
  continuous' := λ c, (continuous_apply i).comp (filtration_pi_homeo M c).continuous,
  map_Tinv' := λ x, rfl,
  .. pi.eval_add_monoid_hom M i }

/-- Universal property of the product of
profinitely filtered pseudo-normed groups with `T⁻¹`-action -/
@[simps {fully_applied := ff}]
def pi_lift {N : Type*} [profinitely_filtered_pseudo_normed_group_with_Tinv r' N]
  (f : Π i, profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' N (M i)) :
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' N (Π i, M i) :=
{ to_fun := add_monoid_hom.mk_to_pi (λ i, (f i).to_add_monoid_hom),
  strict' := λ c x hx i, (f i).strict hx,
  continuous' :=
  begin
    intros c,
    apply continuous_induced_rng,
    apply continuous_pi,
    intro i,
    exact (f i).continuous' c,
  end,
  map_Tinv' := λ x, by { ext i, exact (f i).map_Tinv x },
  .. add_monoid_hom.mk_to_pi (λ i, (f i).to_add_monoid_hom) }

@[simps {fully_applied := ff}]
def pi_map (f : Π i, profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' (M₁ i) (M₂ i)) :
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' (Π i, M₁ i) (Π i, M₂ i) :=
pi_lift r' _ $ λ i, (f i).comp (pi_proj r' _ i)

end

end profinitely_filtered_pseudo_normed_group_with_Tinv
