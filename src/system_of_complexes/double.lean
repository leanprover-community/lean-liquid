import hacks_and_tricks.by_exactI_hack
import system_of_complexes.basic
import normed_group.SemiNormedGroup
import facts

universe variables v u
noncomputable theory
open opposite category_theory
open_locale nnreal

/-!

# Systems of double complexes of seminormed groups

In this file we define systems of double complexes of seminormed groups,
as needed for Definition 9.6 of [Analytic].

## Main declarations

* `system_of_double_complexes`: a system of complexes of seminormed groups.
* `admissible`: such a system is *admissible* if all maps that occur in the system
    are norm-nonincreasing.

-/

/-- A system of double complexes of seminormed groups, indexed by `ℝ≥0`.
See also Definition 9.3 of [Analytic]. -/
@[derive category_theory.category]
def system_of_double_complexes : Type (u+1) :=
ℝ≥0ᵒᵖ ⥤ (cochain_complex ℕ (cochain_complex ℕ SemiNormedGroup.{u}))

namespace system_of_double_complexes

variables (C : system_of_double_complexes)

/-- `C.X c p q` is the object $C_c^{p,q}$ in a system of double complexes `C`. -/
def X (c : ℝ≥0) (p q : ℕ) : SemiNormedGroup :=
((C.obj $ op c).X p).X q

/-- `C.res` is the restriction map `C.X c' p q ⟶ C.X c p q` for a system of complexes `C`,
and nonnegative reals `c ≤ c'`. -/
def res {c' c : ℝ≥0} {p q : ℕ} [h : fact (c ≤ c')] :
  C.X c' p q ⟶ C.X c p q :=
((C.map (hom_of_le h.out).op).f p).f q

variables (c : ℝ≥0) {c₁ c₂ c₃ : ℝ≥0} (p p' q q' : ℕ)

@[simp] lemma res_refl : @res C c c p q _ = 𝟙 _ :=
begin
  have := (category_theory.functor.map_id C (op $ c)),
  delta res, erw this, refl
end

@[simp] lemma norm_res_of_eq (h : c₂ = c₁) (x : C.X c₁ p q) : ∥@res C _ _ p q ⟨h.le⟩ x∥ = ∥x∥ :=
by { cases h, rw res_refl, refl }

@[simp] lemma res_comp_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) :
  @res C _ _ p q h₁ ≫ @res C _ _ p q h₂  = @res C _ _ p q ⟨h₂.out.trans h₁.out⟩ :=
begin
  have := (category_theory.functor.map_comp C (hom_of_le h₁.out).op (hom_of_le h₂.out).op),
  rw [← op_comp] at this,
  delta res, erw this, refl,
end

@[simp] lemma res_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) (x : C.X c₁ p q) :
  @res C _ _ p q h₂ (@res C _ _ p q h₁ x) = @res C _ _ p q ⟨h₂.out.trans h₁.out⟩ x :=
by { rw ← (C.res_comp_res p q h₁ h₂), refl }

/-- `C.d` is the differential `C.X c p q ⟶ C.X c (p+1) q` for a system of double complexes `C`. -/
def d {c : ℝ≥0} (p p' : ℕ) {q : ℕ} : C.X c p q ⟶ C.X c p' q :=
((C.obj $ op c).d p p').f q

lemma d_eq_zero (c : ℝ≥0) (h : p + 1 ≠ p') : (C.d p p' : C.X c p q ⟶ _) = 0 :=
by { have : (C.obj (op c)).d p p' = 0 := (C.obj $ op c).d_eq_zero h, rw [d, this], refl }

lemma d_eq_zero_apply (c : ℝ≥0) (h : p + 1 ≠ p') (x : C.X c p q) : (C.d p p' x) = 0 :=
by { rw [d_eq_zero C p p' q c h], refl }

@[simp] lemma d_self_apply (c : ℝ≥0) (x : C.X c p q) : (C.d p p x) = 0 :=
d_eq_zero_apply _ _ _ _ _ p.succ_ne_self _

lemma d_comp_res (h : fact (c₂ ≤ c₁)) :
  C.d p p' ≫ @res C _ _ _ q h = @res C _ _ p q _ ≫ C.d p p' :=
congr_fun (congr_arg differential_object.hom.f ((C.map (hom_of_le h.out).op).comm p p')) q

lemma d_res (h : fact (c₂ ≤ c₁)) (x) :
  @d C c₂ p p' q (@res C _ _ p q _ x) = @res C _ _ _ _ h (@d C c₁ p p' q x) :=
show (@res C _ _ p q _ ≫ C.d p p') x = (C.d p p' ≫ @res C _ _ _ _ h) x,
by rw d_comp_res

@[simp] lemma d_comp_d {c : ℝ≥0} {p p' p'' q : ℕ} :
  @d C c p p' q ≫ C.d p' p'' = 0 :=
congr_fun (congr_arg differential_object.hom.f ((C.obj $ op c).d_comp_d p p' p'')) q

@[simp] lemma d_d {c : ℝ≥0} {p p' p'' q : ℕ} (x : C.X c p q) :
  C.d p' p'' (C.d p p' x) = 0 :=
show (C.d _ _ ≫ C.d _ _) x = 0, by { rw d_comp_d, refl }

/-- `C.d'` is the differential `C.X c p q ⟶ C.X c p (q+1)` for a system of double complexes `C`. -/
def d' {c : ℝ≥0} {p : ℕ} (q q' : ℕ) : C.X c p q ⟶ C.X c p q' :=
((C.obj $ op c).X p).d q q'

lemma d'_eq_zero (c : ℝ≥0) (h : q + 1 ≠ q') : (C.d' q q' : C.X c p q ⟶ _) = 0 :=
((C.obj $ op c).X p).d_eq_zero h

lemma d'_eq_zero_apply (c : ℝ≥0) (h : q + 1 ≠ q') (x : C.X c p q) : (C.d' q q' x) = 0 :=
by { rw [d'_eq_zero C p q q' c h], refl }

@[simp] lemma d'_self_apply (c : ℝ≥0) (x : C.X c p q) : (C.d' q q x) = 0 :=
d'_eq_zero_apply _ _ _ _ _ q.succ_ne_self _

lemma d'_comp_res (h : fact (c₂ ≤ c₁)) :
  @d' C c₁ p q q' ≫ @res C _ _ _ _ h = @res C _ _ p q _ ≫ @d' C c₂ p q q' :=
((C.map (hom_of_le h.out).op).f p).comm q q'

lemma d'_res (h : fact (c₂ ≤ c₁)) (x) :
  C.d' q q' (@res C _ _ p q _ x) = @res C _ _ _ _ h (C.d' q q' x) :=
show (@res C _ _ p q _ ≫ C.d' q q') x = (C.d' q q' ≫ @res C _ _ _ _ h) x,
by rw d'_comp_res

@[simp] lemma d'_comp_d' {c : ℝ≥0} {p q q' q'' : ℕ} :
  @d' C c p q q' ≫ C.d' q' q'' = 0 :=
((C.obj $ op c).X p).d_comp_d q q' q''

@[simp] lemma d'_d' {c : ℝ≥0} {p q q' q'' : ℕ} (x : C.X c p q) :
  C.d' q' q'' (C.d' q q' x) = 0 :=
show (C.d' _ _ ≫ C.d' _ _) x = 0, by { rw d'_comp_d', refl }

lemma d'_comp_d (c : ℝ≥0) (p p' q q' : ℕ) :
  C.d' q q' ≫ C.d p p' = C.d p p' ≫ (C.d' q q' : C.X c p' q ⟶ _) :=
((C.obj $ op c).d p p').comm q q'

lemma d'_d (c : ℝ≥0) (p p' q q' : ℕ) (x : C.X c p q) :
  C.d' q q' (C.d p p' x) = C.d p p' (C.d' q q' x) :=
show (C.d p p' ≫ C.d' q q') x = (C.d' q q' ≫ C.d p p') x,
by rw [d'_comp_d]

/-- Convenience definition:
The identity morphism of an object in the system of double complexes
when it is given by different indices that are not
definitionally equal. -/
def congr {c c' : ℝ≥0} {p p' q q' : ℕ} (hc : c = c') (hp : p = p') (hq : q = q') :
  C.X c p q ⟶ C.X c' p' q' :=
eq_to_hom $ by { subst hc, subst hp, subst hq, }

-- attribute [simps] differential_object.forget

/-- The `p`-th row in a system of double complexes, as system of complexes.
  It has object `(C.obj c).X p`over `c`. -/
def row (C : system_of_double_complexes.{u}) (p : ℕ) : system_of_complexes.{u} :=
C ⋙ induced_functor _ ⋙ differential_object.forget _ _ ⋙ pi.eval _ p

@[simp] lemma row_X (C : system_of_double_complexes) (p q : ℕ) (c : ℝ≥0) :
  C.row p c q = C.X c p q :=
rfl

@[simp] lemma row_res (C : system_of_double_complexes) (p q : ℕ) {c' c : ℝ≥0} [h : fact (c ≤ c')] :
  @system_of_complexes.res (C.row p) _ _ q h  = @res C _ _ p q h :=
rfl

@[simp] lemma row_d (C : system_of_double_complexes) (c : ℝ≥0) (p : ℕ) :
  (C.row p).d = @d' C c p :=
rfl

/-- The differential between rows in a system of double complexes,
as map of system of complexes. -/
@[simps app_f]
def row_map (C : system_of_double_complexes.{u}) (p p' : ℕ) :
  C.row p ⟶ C.row p' :=
{ app := λ c,
  { f := λ q, (C.d p p' : C.X c.unop p q ⟶ C.X c.unop p' q),
    comm := λ q q', (C.d'_comp_d _ p p' q q') },
  naturality' := λ c₁ c₂ h, ((C.map h).comm p p').symm }

@[simp] lemma row_map_apply (C : system_of_double_complexes.{u})
  (c : ℝ≥0) (p p' q : ℕ) (x : C.X c p q) :
  C.row_map p p' x = C.d p p' x := rfl

/-- The `q`-th column in a system of double complexes, as system of complexes. -/
def col (C : system_of_double_complexes.{u}) (q : ℕ) : system_of_complexes.{u} :=
C ⋙ functor.map_complex_like' (induced_functor _ ⋙ differential_object.forget _ _ ⋙ pi.eval _ q)
  (by { intros, ext, refl })

@[simp] lemma col_X (C : system_of_double_complexes) (p q : ℕ) (c : ℝ≥0) :
  C.col q c p = C.X c p q :=
rfl

@[simp] lemma col_res (C : system_of_double_complexes) (p q : ℕ) {c' c : ℝ≥0} [h : fact (c ≤ c')] :
  @system_of_complexes.res (C.col q) _ _ _ _ = @res C _ _ p q h :=
rfl

@[simp] lemma col_d (C : system_of_double_complexes) (c : ℝ≥0) (p p' q : ℕ) :
  (C.col q).d p p' = @d C c p p' q :=
rfl

/-- The differential between columns in a system of double complexes,
as map of system of complexes. -/
def col_map (C : system_of_double_complexes.{u}) (q q' : ℕ) :
  C.col q ⟶ C.col q' :=
{ app := λ c,
  { f := λ p, (C.d' q q' : C.X c.unop p q ⟶ C.X c.unop p q'),
    comm := λ p p', (C.d'_comp_d _ p p' q q').symm },
  naturality' := λ c₁ c₂ h, by { ext p : 2, exact (((C.map h).f p).comm q q').symm } }

/-- A system of double complexes is *admissible*
if all the differentials and restriction maps are norm-nonincreasing.

See Definition 9.3 of [Analytic]. -/
structure admissible (C : system_of_double_complexes) : Prop :=
(d_norm_noninc' : ∀ c p p' q (h : p + 1 = p'), (@d C c p p' q).norm_noninc)
(d'_norm_noninc' : ∀ c p q q' (h : q + 1 = q'), (@d' C c p q q').norm_noninc)
(res_norm_noninc : ∀ c' c p q h, (@res C c' c p q h).norm_noninc)

namespace admissible

variables {C}

lemma d_norm_noninc (hC : C.admissible) (c : ℝ≥0) (p p' q : ℕ) :
  (C.d p p' : C.X c p q ⟶ _).norm_noninc :=
begin
  by_cases h : p + 1 = p',
  { exact hC.d_norm_noninc' c p p' q h },
  { rw C.d_eq_zero p p' q c h, intro v, simp }
end

lemma d'_norm_noninc (hC : C.admissible) (c : ℝ≥0) (p q q' : ℕ) :
  (C.d' q q' : C.X c p q ⟶ _).norm_noninc :=
begin
  by_cases h : q + 1 = q',
  { exact hC.d'_norm_noninc' c p q q' h },
  { rw C.d'_eq_zero p q q' c h, intro v, simp }
end

lemma col (hC : C.admissible) (q : ℕ) : (C.col q).admissible :=
{ d_norm_noninc' := λ c i j h, hC.d_norm_noninc _ _ _ _,
  res_norm_noninc := λ c i j h, hC.res_norm_noninc _ _ _ _ _ }

lemma row (hC : C.admissible) (p : ℕ) : (C.row p).admissible :=
{ d_norm_noninc' := λ c i j h, hC.d'_norm_noninc _ _ _ _,
  res_norm_noninc := λ c i j h, hC.res_norm_noninc _ _ _ _ _ }

lemma mk' (h : ∀ p, (C.row p).admissible)
  (hd : ∀ c p p' q (h : p + 1 = p'), (@d C c p p' q).norm_noninc) :
  C.admissible :=
{ d_norm_noninc' := λ c p p' q h', hd c p p' q h',
  d'_norm_noninc' := λ c p q q' h', (h p).d_norm_noninc' _ _ _ h',
  res_norm_noninc := λ c₁ c₂ p q h', by { resetI, apply (h p).res_norm_noninc } }

end admissible

end system_of_double_complexes
