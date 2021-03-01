import algebra.homology.chain_complex
import hacks_and_tricks.by_exactI_hack
import system_of_complexes.basic
import normed_group.NormedGroup
import facts

universe variables v u
noncomputable theory
open opposite category_theory
open_locale nnreal

/-!
# Systems of double complexes of normed abelian groups

In this file we define systems of double complexes of normed abelian groups,
as needed for Definition 9.6 of [Analytic].

## Main declarations

* `system_of_double_complexes`: a system of complexes of normed abelian groups.
* `admissible`: such a system is *admissible* if all maps that occur in the system
    are norm-nonincreasing.
-/

/-- A system of double complexes of normed abelian groups, indexed by `ℝ≥0`.
See also Definition 9.3 of [Analytic].

Implementation detail: `cochain_complex` assumes that the complex is indexed by `ℤ`,
whereas we are interested in complexes indexed by `ℕ`.
We therefore set all objects indexed by negative integers to `0`, in our use case. -/
@[derive category_theory.category]
def system_of_double_complexes : Type (u+1) :=
ℝ≥0ᵒᵖ ⥤ (cochain_complex (cochain_complex NormedGroup.{u}))

namespace system_of_double_complexes

variables (C : system_of_double_complexes)

/-- `C.X c p q` is the object $C_c^{p,q}$ in a system of double complexes `C`. -/
def X (c : ℝ≥0) (p q : ℤ) : NormedGroup :=
((C.obj $ op c).X p).X q

/-- `C.res` is the restriction map `C.X c' p q ⟶ C.X c p q` for a system of complexes `C`,
and nonnegative reals `c ≤ c'`. -/
def res {c' c : ℝ≥0} {p q : ℤ} [h : fact (c ≤ c')] :
  C.X c' p q ⟶ C.X c p q :=
((C.map (hom_of_le h).op).f p).f q

variables (c : ℝ≥0) {c₁ c₂ c₃ : ℝ≥0} (p q : ℤ)

@[simp] lemma res_refl : @res C c c p q _ = 𝟙 _ :=
begin
  have := (category_theory.functor.map_id C (op $ c)),
  delta res, erw this, refl
end

@[simp] lemma res_comp_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) :
  @res C _ _ p q h₁ ≫ @res C _ _ p q h₂  = @res C _ _ p q (le_trans h₂ h₁) :=
begin
  have := (category_theory.functor.map_comp C (hom_of_le h₁).op (hom_of_le h₂).op),
  rw [← op_comp] at this,
  delta res, erw this, refl,
end

@[simp] lemma res_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) (x : C.X c₁ p q) :
  @res C _ _ p q h₂ (@res C _ _ p q h₁ x) = @res C _ _ p q (le_trans h₂ h₁) x :=
by { rw ← (C.res_comp_res p q h₁ h₂), refl }

/-- `C.d` is the differential `C.X c p q ⟶ C.X c (p+1) q` for a system of double complexes `C`. -/
def d {c : ℝ≥0} {p q : ℤ} :
  C.X c p q ⟶ C.X c (p+1) q :=
((C.obj $ op c).d p).f q

lemma d_comp_res (h : fact (c₂ ≤ c₁)) :
  @d C c₁ p q ≫ @res C _ _ _ _ h = @res C _ _ p q _ ≫ @d C c₂ p q :=
begin
  have step1 := (homological_complex.comm_at (C.map (hom_of_le h).op) p),
  have step2 := congr_arg differential_object.hom.f step1,
  exact congr_fun step2 q
end

lemma d_res (h : fact (c₂ ≤ c₁)) (x) :
  @d C c₂ p q (@res C _ _ p q _ x) = @res C _ _ _ _ h (@d C c₁ p q x) :=
show (@res C _ _ p q _ ≫ @d C c₂ p q) x = (@d C c₁ p q ≫ @res C _ _ _ _ h) x,
by rw d_comp_res

@[simp] lemma d_comp_d {c : ℝ≥0} {p q : ℤ} :
  @d C c p q ≫ C.d = 0 :=
begin
  have step1 := (homological_complex.d_squared (C.obj $ op c)) p,
  have step2 := congr_arg differential_object.hom.f step1,
  exact congr_fun step2 q
end

@[simp] lemma d_d {c : ℝ≥0} {p q : ℤ} (x : C.X c p q) :
  C.d (C.d x) = 0 :=
show (@d C c _ _ ≫ C.d) x = 0, by { rw d_comp_d, refl }

/-- `C.d'` is the differential `C.X c p q ⟶ C.X c p (q+1)` for a system of double complexes `C`. -/
def d' {c : ℝ≥0} {p q : ℤ} :
  C.X c p q ⟶ C.X c p (q+1) :=
((C.obj $ op c).X p).d q

lemma d'_comp_res (h : fact (c₂ ≤ c₁)) :
  @d' C c₁ p q ≫ @res C _ _ _ _ h = @res C _ _ p q _ ≫ @d' C c₂ p q :=
homological_complex.comm_at ((C.map (hom_of_le h).op).f p) q

lemma d'_res (h : fact (c₂ ≤ c₁)) (x) :
  @d' C c₂ p q (@res C _ _ p q _ x) = @res C _ _ _ _ h (@d' C c₁ p q x) :=
show (@res C _ _ p q _ ≫ @d' C c₂ p q) x = (@d' C c₁ p q ≫ @res C _ _ _ _ h) x,
by rw d'_comp_res

@[simp] lemma d'_comp_d' {c : ℝ≥0} {p q : ℤ} :
  @d' C c p q ≫ C.d' = 0 :=
((C.obj $ op c).X p).d_squared q

@[simp] lemma d'_d' {c : ℝ≥0} {p q : ℤ} (x : C.X c p q) :
  C.d' (C.d' x) = 0 :=
show (@d' C c _ _ ≫ C.d') x = 0, by { rw d'_comp_d', refl }

/-- Convenience definition:
The identity morphism of an object in the system of double complexes
when it is given by different indices that are not
definitionally equal. -/
def congr {c c' : ℝ≥0} {p p' q q' : ℤ} (hc : c = c') (hp : p = p') (hq : q = q') :
  C.X c p q ⟶ C.X c' p' q' :=
eq_to_hom $ by { subst hc, subst hp, subst hq, }

/-- A system of double complexes is *admissible*
if all the differentials and restriction maps are norm-nonincreasing.

See Definition 9.3 of [Analytic]. -/
structure admissible (C : system_of_double_complexes) : Prop :=
(d_norm_noninc : ∀ c p q (x : C.X c p q), ∥C.d x∥ ≤ ∥x∥)
(d'_norm_noninc : ∀ c p q (x : C.X c p q), ∥C.d' x∥ ≤ ∥x∥)
(res_norm_noninc : ∀ c' c p q h (x : C.X c' p q), ∥@res C c' c p q h x∥ ≤ ∥x∥)

attribute [simps] differential_object.forget

/-- The `p`-th row in a system of double complexes, as system of complexes.
  It has object `(C.obj c).X p`over `c`. -/
def row (C : system_of_double_complexes) (p : ℤ) : system_of_complexes :=
C.comp ((homological_complex.forget _).comp $ pi.eval _ p)

@[simp] lemma row_X (C : system_of_double_complexes) (p q : ℤ) (c : ℝ≥0) :
  C.row p c q = C.X c p q :=
by refl

@[simp] lemma row_res (C : system_of_double_complexes) (p q : ℤ) {c' c : ℝ≥0} [h : fact (c ≤ c')] :
  @system_of_complexes.res (C.row p) _ _ q h  = @res C _ _ p q h :=
by refl

@[simp] lemma row_d (C : system_of_double_complexes) (p q : ℤ) (c : ℝ≥0) :
  @system_of_complexes.d (C.row p) _ _ = @d' C c p q :=
by refl

/-- The `q`-th column in a system of double complexes, as system of complexes. -/
def col (C : system_of_double_complexes) (q : ℤ) : system_of_complexes :=
C.comp
  (functor.map_differential_object _
    (functor.pi $ λ n, (homological_complex.forget _).comp $ pi.eval _ q)
    { app := λ X, 𝟙 _, naturality' := by { intros, ext, simp } }
    (by { intros, ext, simp }))

@[simp] lemma col_X (C : system_of_double_complexes) (p q : ℤ) (c : ℝ≥0) :
  C.col q c p = C.X c p q :=
by refl

@[simp] lemma col_res (C : system_of_double_complexes) (p q : ℤ) {c' c : ℝ≥0} [h : fact (c ≤ c')] :
  @system_of_complexes.res (C.col q) _ _ _ _ = @res C _ _ p q h :=
by refl

@[simp] lemma col_d (C : system_of_double_complexes) (p q : ℤ) (c : ℝ≥0) :
  @system_of_complexes.d (C.col q) _ _ = @d C c p q :=
by { dsimp [system_of_complexes.d, col, d], simp }

/-- The assumptions on `M` in Proposition 9.6 bundled into a structure. Note that in `cond3b`
  our `q` is one smaller than the `q` in the notes (so that we don't have to deal with `q - 1`). -/
structure normed_spectral_conditions (m : ℕ) (k K : ℝ≥0) [fact (1 ≤ k)]
  (ε : ℝ) (hε : 0 < ε) (k₀ : ℝ≥0) [fact (1 ≤ k₀)]
  (M : system_of_double_complexes)
  (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] (c₀ H : ℝ≥0) [fact (0 < H)] :=
(col_exact : ∀ j ≤ m, (M.col j).is_bounded_exact k K (m+1) c₀)
(row_exact : ∀ i ≤ m + 1, (M.row i).is_bounded_exact k K m c₀)
(h : Π {q : ℤ} [fact (q ≤ m)] {c} [fact (c₀ ≤ c)], M.X (k' * c) 0 (q+1) ⟶ M.X c 1 q)
(norm_h_le : ∀ (q : ℤ) [fact (q ≤ m)] (c) [fact (c₀ ≤ c)] (x : M.X (k' * c) 0 (q+1)), ​∥h x∥ ≤ H * ∥x∥)
(cond3b : ∀ (q : ℤ) [fact (q+1 ≤ m)] (c) [fact (c₀ ≤ c)]
  (x : M.X (k' * (k' * c)) 0 (q+1)) (u1 u2 : units ℤ),
  ​∥M.res (M.d x) + (u1:ℤ) • h (M.d' x) + (u2:ℤ) • M.d' (h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥)
.

namespace normed_spectral_conditions

variables (m : ℕ) (k K : ℝ≥0) [fact (1 ≤ k)]
variables (ε : ℝ) (hε : 0 < ε) (k₀ : ℝ≥0) [fact (1 ≤ k₀)]
variables (M : system_of_double_complexes.{u})
variables (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] (c₀ H : ℝ≥0) [fact (0 < H)]

lemma cond3bpp (NSC : normed_spectral_conditions.{u u} m k K ε hε k₀ M k' c₀ H)
  (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
  ​∥M.res (M.d x) + NSC.h (M.d' x) + M.d' (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
by simpa only [units.coe_one, one_smul] using NSC.cond3b q c x 1 1

lemma cond3bpm (NSC : normed_spectral_conditions.{u u} m k K ε hε k₀ M k' c₀ H)
  (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
  ​∥M.res (M.d x) + NSC.h (M.d' x) - M.d' (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
by simpa only [units.coe_one, one_smul, neg_smul, units.coe_neg, ← sub_eq_add_neg]
  using NSC.cond3b q c x 1 (-1)

lemma cond3bmp (NSC : normed_spectral_conditions.{u u} m k K ε hε k₀ M k' c₀ H)
  (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
  ​∥M.res (M.d x) - NSC.h (M.d' x) + M.d' (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
by simpa only [units.coe_one, one_smul, neg_smul, units.coe_neg, ← sub_eq_add_neg]
  using NSC.cond3b q c x (-1) 1

lemma cond3bmm (NSC : normed_spectral_conditions.{u u} m k K ε hε k₀ M k' c₀ H)
  (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
  ​∥M.res (M.d x) - NSC.h (M.d' x) - M.d' (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
by simpa only [units.coe_one, one_smul, neg_smul, units.coe_neg, ← sub_eq_add_neg]
  using NSC.cond3b q c x (-1) (-1)

end normed_spectral_conditions

/-- Proposition 9.6 in [Analytic]
Constants (max (k' * k') (2 * k₀ * H)) and K in the statement are not the right ones.
We need to investigate the consequences of the k Zeeman effect here.
-/
theorem analytic_9_6 (m : ℕ) (k K : ℝ≥0) [fact (1 ≤ k)] :
  ∃ (ε : ℝ) (hε : ε > 0) (k₀ : ℝ≥0) [fact (1 ≤ k₀)],
  ∀ (M : system_of_double_complexes) (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] -- follows
    (c₀ H : ℝ≥0) [fact (0 < H)],
  ​∀ (cond : normed_spectral_conditions m k K ε hε k₀ M k' c₀ H),
  (M.row 0).is_bounded_exact (max (k' * k') (2 * k₀ * H)) K (m+1) c₀ :=
begin
  induction m with m hm,
  { -- base case m = 0
    -- ε = 1/(2k) works
    use [1/(2*k)],
    existsi _, swap,
    { have hk : 1 ≤ k := fact.elim (by apply_instance),
      rw [gt_iff_lt, one_div, inv_pos],
      refine mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (by assumption_mod_cast)) },
    -- k₀ = k works
    use k,
    use (by assumption),
    intros,
    resetI,
    let cond_row_exact := normed_spectral_conditions.row_exact cond,
    intros c hc i hi x,
    change i < 1 at hi,
    -- Statement is of the form "for all x ∈ M_{0,i+1} exists y ∈ M_{0,i} such that..."
    -- Cases i<-1 are trivial because x=y=0 works.
    cases lt_or_le i (-1 : ℤ) with h h,
    { -- this should deal with -1
      use 0,
      rw lt_neg_iff_add_neg at h,
      have hx : (M.row 0) (max (k' * k') (2 * k * H) * c) (i + 1) = 0,
      { -- this should be an assumption?
        sorry },
      -- goal should be 0 ≤ 0
      sorry },
    -- cases i = -1 and i = 0 left
    { sorry }
  },
  { -- inductive step
    sorry }
end

end system_of_double_complexes
