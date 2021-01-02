import Mbar.Mbar_le
import breen_deligne
import normed_group_hom

local attribute [instance] type_pow

noncomputable theory

open_locale big_operators nnreal

-- move this
instance normed_group_pow (V : Type*) (n : ℕ) [normed_group V] :
  normed_group (V^n) :=
pi.normed_group

namespace Mbar_le

variables (r' : ℝ) (S : Type*) [fintype S] [fact (0 < r')]

def hom_of_normed_group_hom' {C : ℝ≥0} (c₁ c₂ : ℝ) {m n : ℕ} [fact (0 ≤ c₁)] (hc : ↑C * c₁ ≤ c₂)
  (f : normed_group_hom ((Mbar r' S)^m) ((Mbar r' S)^n)) (h : f.bound_by C)
  (F : (Mbar_le r' S c₁)^m) :
  (Mbar_le r' S c₂)^n :=
λ j,
({to_fun := λ s i, f (λ k, (F k).to_Mbar) j s i,
  coeff_zero' := λ s, Mbar.coeff_zero _ _,
  summable' := λ s, Mbar.summable _ _,
  sum_tsum_le' :=
  begin
    calc ∥f (λ k, (F k).to_Mbar) j∥
        ≤ ∥f (λ k, (F k).to_Mbar)∥ : norm_le_pi_norm (f (λ k, (F k).to_Mbar)) j
    ... ≤ C * ∥_∥ : h _
    ... ≤ C * c₁ : mul_le_mul le_rfl _ (norm_nonneg _) C.coe_nonneg
    ... ≤ c₂ : hc,
    rw pi_norm_le_iff ‹0 ≤ c₁›,
    intro i,
    apply Mbar_le.sum_tsum_le
  end } : Mbar_le r' S c₂)

lemma continuous_of_normed_group_hom' (c₁ c₂ : ℝ) {m n : ℕ}
  [fact (0 ≤ c₁)] [fact (0 ≤ c₂)]
  (f : normed_group_hom ((Mbar r' S) ^ m) ((Mbar r' S) ^ n))
  (g : (Mbar_le r' S c₁)^m → (Mbar_le r' S c₂)^n)
  (h : ∀ x j, (g x j).to_Mbar = f (λ i, (x i).to_Mbar) j)
  (H : ∀ M : ℕ, ∃ N : ℕ, ∀ (F : (Mbar r' S)^m),
    (∀ i s k, k < N + 1 → (F i : Mbar r' S) s k = 0) → (∀ j s k, k < M + 1 → f F j s k = 0)) :
  continuous g :=
begin
  apply continuous_pi,
  intro j,
  rw continuous_iff,
  intros M,
  rcases H M with ⟨N, hN⟩,
  let φ : (Mbar_bdd r' ⟨S⟩ c₁ N)^m → (Mbar_le r' S c₁)^m :=
    function.comp (classical.some (truncate_surjective N).has_right_inverse),
  have hφ : function.right_inverse φ (function.comp $ truncate N),
  { intro x, ext1 i,
    exact (classical.some_spec (truncate_surjective N).has_right_inverse) (x i) },
  suffices :
    truncate M ∘ (λ F, g F j) = truncate M ∘ (λ F, g F j) ∘ φ ∘ (function.comp $ truncate N),
  { rw [this, ← function.comp.assoc, ← function.comp.assoc],
    refine continuous.comp _ (continuous_pi _),
    { -- we need an instance of `discrete_topology (Π i, X i)` for finite products
      /- convert continuous_bot -/
      sorry },
    { intro i, exact continuous_truncate.comp (continuous_apply _) } },
  ext1 x,
  suffices : ∀ s k, k < M + 1 → (g x j).to_Mbar s k = (g (φ (λ i, truncate N (x i))) j).to_Mbar s k,
  { ext s k, dsimp [function.comp], apply this, exact k.property },
  intros s k hk,
  rw [h, h, ← sub_eq_zero],
  show (f (λ i, (x i).to_Mbar) - f (λ i, (φ (λ i', truncate N (x i')) i).to_Mbar)) j s k = 0,
  rw [← f.map_sub],
  apply hN _ _ _ _ _ hk,
  clear hk k s, intros i s k hk,
  simp only [Mbar.coe_sub, pi.sub_apply, sub_eq_zero],
  suffices : ∀ k, (truncate N (x i)) s k = truncate N (φ (λ i', truncate N (x i')) i) s k,
  { exact this ⟨k, hk⟩ },
  intros k, congr' 1, revert i, rw ← function.funext_iff,
  exact (hφ _).symm
end

def hom_of_normed_group_hom'_continuous
  {C : ℝ≥0} (c₁ c₂ : ℝ) {m n : ℕ} [fact (0 ≤ c₁)] [fact (0 ≤ c₂)] (hc : ↑C * c₁ ≤ c₂)
  (f : normed_group_hom ((Mbar r' S)^m) ((Mbar r' S)^n)) (h : f.bound_by C)
  (H : ∀ M : ℕ, ∃ N : ℕ, ∀ (F : (Mbar r' S)^m),
    (∀ i s k, k < N + 1 → (F i : Mbar r' S) s k = 0) → (∀ j s k, k < M + 1 → f F j s k = 0)) :
  continuous (hom_of_normed_group_hom' r' S c₁ c₂ hc f h) :=
continuous_of_normed_group_hom' r' S c₁ c₂ f _ (λ x i, by { ext, refl }) H

end Mbar_le

open normed_group_hom normed_group

namespace breen_deligne

namespace basic_universal_map

variables {k m n : ℕ}
variables (r' : ℝ) (S : Type*) (c₁ c₂ : ℝ) [fintype S] [fact (0 < r')] [fact (0 ≤ c₁)]
variables (f : basic_universal_map m n)

def eval_Mbar : normed_group_hom ((Mbar r' S)^m) ((Mbar r' S)^n) :=
mk_to_pi' _
(λ i, mk_from_pi' _ _ (λ j, gsmul (f i j)) (λ j, real.nnabs (f i j)) $ (λ j, gsmul_bound_by _))
(λ i, ∑ j, real.nnabs (f i j)) $ λ i, mk_from_pi'_bound_by _ _ _ _ _

@[simp] lemma eval_Mbar_zero : (eval_Mbar r' S (0 : basic_universal_map m n)) = 0 :=
begin
  ext F i s k,
  sorry
end

@[simp] lemma eval_Mbar_comp (g : basic_universal_map m n) (f : basic_universal_map k m) :
  (g.comp f).eval_Mbar r' S = (g.eval_Mbar r' S).comp (f.eval_Mbar r' S) :=
begin
  ext F i s ℓ,
  -- simp only [eval_Mbar, normed_group_hom.mk_from_pi_to_fun, add_monoid_hom.coe_comp,
  --   normed_group_hom.comp_to_fun, add_monoid_hom.to_fun_eq_coe, function.comp_app,
  --   normed_group.gsmul_to_fun, normed_group_hom.mk_to_pi_to_fun,
  --   normed_group_hom.mk_to_pi, normed_group_hom.mk_from_pi],
  dsimp,
  sorry
end

lemma eval_Mbar_bound_by :
  (f.eval_Mbar r' S).bound_by (finset.univ.sup $ λ i, ∑ j, real.nnabs (f i j)) :=
normed_group_hom.mk_to_pi'_bound_by _ _ _ _

/-- Addition goes from `Mbar r' S c` to `Mbar r' S c'` for suitable `c'`.
This predicate says what *suitable* means for basic universal maps.
See Lemma 9.11 of [Analytic]. -/
def suitable (f : basic_universal_map m n) (c₁ c₂ : ℝ) : Prop :=
↑(finset.univ.sup (λ (i : fin n), ∑ (j : fin m), real.nnabs ↑(f i j))) * c₁ ≤ c₂

def eval_Mbar_le [H : fact (f.suitable c₁ c₂)] :
  ((Mbar_le r' S c₁)^m) → ((Mbar_le r' S c₂)^n) :=
Mbar_le.hom_of_normed_group_hom' r' S c₁ c₂ H (f.eval_Mbar r' S) $ f.eval_Mbar_bound_by r' S

lemma eval_Mbar_le_continuous [fact (0 ≤ c₂)] [H : fact (f.suitable c₁ c₂)] :
  continuous (f.eval_Mbar_le r' S c₁ c₂) :=
Mbar_le.hom_of_normed_group_hom'_continuous _ _ _ _ H _ _ $
begin
  intro M, sorry
  -- we should probably prove this for `mk_to_pi'` and `mk_from_pi'` first
end

end basic_universal_map

namespace universal_map

variables {m n : ℕ}
variables (r' : ℝ) (S : Type*) [fintype S] [fact (0 < r')]

def eval_Mbar : universal_map m n →+ normed_group_hom ((Mbar r' S)^m) ((Mbar r' S)^n) :=
free_abelian_group.lift $ basic_universal_map.eval_Mbar _ _

end universal_map

end breen_deligne
