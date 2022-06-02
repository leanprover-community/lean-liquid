import algebra.homology.homological_complex
import algebra.homology.single
import category_theory.abelian.basic
import for_mathlib.split_exact
import for_mathlib.derived.defs

noncomputable theory

open category_theory category_theory.limits

namespace cochain_complex

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables (C : cochain_complex 𝓐 ℤ)

local attribute [instance] has_zero_object.has_zero -- isn't there a locale which does this??

/--
Given a cochain complex
```
C^{n-2} → C^{n-1} → C^n → C^{n+1}
```
`imker C n` should be the cochain complex
```
   0  → Im(d^n) → Ker(d^n) → 0
```
As a result, `H_i(imker C n) = 0` for all `i≠n` and `= H_i(C)` for `i=n`.
-/
def imker (C : cochain_complex 𝓐 ℤ) (n : ℤ) : cochain_complex 𝓐 ℤ :=
{ X := λ i, if i = n-1 then image_subobject (C.d_to n) else
  if i = n then kernel_subobject (C.d_from n) else 0,
  d := λ i j, if hi : i = n - 1 then if hj : j = n then
    (eq_to_iso (by rw [hi, if_pos rfl]) : ((if i = n-1 then image_subobject (C.d_to n) else
  if i = n then kernel_subobject (C.d_from n) else 0) : 𝓐) ≅ image_subobject (C.d_to n)).hom ≫
    image_to_kernel _ _ (homological_complex.d_to_comp_d_from _ n) ≫
            (eq_to_iso begin rw [if_neg, if_pos hj], linarith, end :
              (kernel_subobject (C.d_from n) : 𝓐) ≅ _).hom
          else 0
        else 0,
  shape' := begin
    rintro i j (h : _ ≠ _),
    split_ifs with hi,
    { rw dif_neg,
      rintro rfl,
      exact (h (add_eq_of_eq_sub hi)).elim, },
    { refl },
  end,
  d_comp_d' := begin
    rintro i j k (rfl : _ = _) (rfl : _ = _),
    split_ifs with hi hn,
    { subst hi,
      simp only [add_right_eq_self, one_ne_zero, not_false_iff, dif_neg, comp_zero]},
    { apply zero_comp, },
  end }

namespace imker

open homological_complex (single)

lemma X_def {n i : ℤ} : (imker C n).X i =
if i = n-1 then image_subobject (C.d_to n) else
  if i = n then kernel_subobject (C.d_from n) else
    (has_zero_object.has_zero 𝓐).zero :=
rfl

@[simps] def X_iso_image (n : ℤ) : (imker C n).X (n-1) ≅ image_subobject (C.d_to n) :=
eq_to_iso (by {rw [X_def, if_pos rfl]})

@[simps] def X_iso_image_of_eq {n i : ℤ} (h : i = n - 1) : (imker C n).X i ≅ image_subobject (C.d_to n) :=
eq_to_iso (by {rw [X_def, if_pos h]})

@[simps] def X_iso_kernel (n : ℤ) : (imker C n).X n ≅ kernel_subobject (C.d_from n) :=
eq_to_iso (by {rw [X_def, if_neg, if_pos rfl], linarith})

@[simps] def X_iso_kernel_of_eq {n i : ℤ} (h : i = n) : (imker C n).X i ≅ kernel_subobject (C.d_from n) :=
eq_to_iso (by {rw [X_def, if_neg, if_pos h], linarith})

@[simps] def kernel_iso_X_of_eq {n i : ℤ} (h : i = n) :
  (kernel_subobject (C.d_from n) : 𝓐) ≅ (imker C n).X i :=
eq_to_iso (by {rw [X_def, if_neg, if_pos h], linarith})

lemma X_is_zero_of_ne {i j : ℤ} (h1 : j ≠ i - 1) (h2 : j ≠ i) : is_zero ((C.imker i).X j) :=
begin
  rw [X_def, if_neg h1, if_neg h2],
  exact is_zero_zero 𝓐,
end

@[simp] lemma d_def {n i j : ℤ} : (imker C n).d i j = if hi : i = n - 1 then if hj : j = n then
    (eq_to_iso (by rw [hi, if_pos rfl]) : ((if i = n-1 then image_subobject (C.d_to n) else
  if i = n then kernel_subobject (C.d_from n) else 0) : 𝓐) ≅ image_subobject (C.d_to n)).hom ≫
    image_to_kernel _ _ (homological_complex.d_to_comp_d_from _ n) ≫
            (eq_to_iso begin dsimp only [imker], rw [if_neg, if_pos hj], linarith, end :
              (kernel_subobject (C.d_from n) : 𝓐) ≅ _).hom
          else 0
        else 0 :=
rfl

lemma d_interesting {n i j : ℤ} (h : i = n - 1) (hj : j = n) : (imker C n).d i j =
(X_iso_image_of_eq C h).hom ≫
image_to_kernel _ _ (homological_complex.d_to_comp_d_from _ n) ≫ (X_iso_kernel_of_eq _ hj).inv :=
begin
  simp only [h, hj, eq_self_iff_true, d_def, eq_to_iso.hom, dif_pos, X_iso_image_of_eq_hom,
    X_iso_kernel_of_eq_inv],
  refl,
end

lemma bounded_by (i : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.imker i)).bounded_by (i+1) :=
begin
  intros j hj,
  simp only [homotopy_category.quotient_obj_as],
  apply X_is_zero_of_ne;
  linarith,
end

instance is_bounded_above (i : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.imker i)).is_bounded_above :=
⟨⟨i+1, bounded_by C i⟩⟩

/-- The natural map from `imker C n` to `H_n(C)[n]`. -/
def to_single (n : ℤ) : C.imker n ⟶ (single _ _ n).obj (C.homology n) :=
{ f := λ i, if h : i = n then (X_iso_kernel_of_eq C h).hom ≫
  cokernel.π (image_to_kernel _ _ (homological_complex.d_to_comp_d_from _ n)) ≫
 (homological_complex.single_obj_X_self 𝓐 (complex_shape.up ℤ) n _).inv ≫
 (eq_to_iso (begin rw h, refl, end)).hom else 0,
  comm' := begin
   rintro i j (rfl : _ = _),
   simp only [homological_complex.single_obj_X_self_inv, eq_to_iso.hom, eq_to_hom_trans,
     homological_complex.single_obj_d, comp_zero],
   split_ifs with hi hn,
   { subst hi, clear hn,
     rw d_interesting C (show i = i + 1 - 1, by ring) rfl,
     simp only [category.assoc, iso.inv_hom_id_assoc, cokernel.condition_assoc, zero_comp,
       comp_zero], },
   { exact (hn rfl).elim },
   { rw comp_zero },
  end }

instance to_single_quasi_iso (n : ℤ) :
  homotopy_category.is_quasi_iso $ (homotopy_category.quotient _ _).map (to_single C n) :=
sorry

end imker

/--
This should be the canonical truncation functor `τ_{≤n}` for cochain complexes.
It is the functor (3) in the second set of truncation functors on this page:
https://stacks.math.columbia.edu/tag/0118
-/
def truncation (C : cochain_complex 𝓐 ℤ) (i : ℤ) : cochain_complex 𝓐 ℤ :=
sorry

namespace truncation

lemma bounded_by (i : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.truncation i)).bounded_by (i+1) :=
sorry

instance is_bounded_above (i : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.truncation i)).is_bounded_above :=
⟨⟨i+1, bounded_by C i⟩⟩

def ι (i : ℤ) : C.truncation i ⟶ C :=
sorry

lemma ι_iso (i : ℤ) (hC : ((homotopy_category.quotient _ _).obj C).bounded_by (i+1)) :
  is_iso (truncation.ι C i) :=
sorry

-- feel free to skip this, and directly provide a defn for `ι_succ` below
def map_of_le (i j : ℤ) (h : i ≤ j) : C.truncation i ⟶ C.truncation j :=
sorry

def ι_succ (i : ℤ) : C.truncation i ⟶ C.truncation (i+1) :=
truncation.map_of_le _ _ _ $ by simp only [le_add_iff_nonneg_right, zero_le_one]

def to_imker (i : ℤ) : C.truncation i ⟶ imker C i :=
sorry

lemma short_exact_ι_succ_to_imker (i : ℤ) :
  ∀ n, short_exact ((ι_succ C i).f n) ((to_imker C (i+1)).f n) :=
sorry

end truncation

end cochain_complex
