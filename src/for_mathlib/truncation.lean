import for_mathlib.imker

noncomputable theory

open category_theory category_theory.limits

namespace cochain_complex

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables (C : cochain_complex 𝓐 ℤ)

open_locale zero_object

--This should be the canonical truncation functor `τ_{≤n}` for cochain complexes.
--It is the functor (3) in the second set of truncation functors on this page:
--https://stacks.math.columbia.edu/tag/0118

/-- The "canonical truncation" of a cochain complex (Cⁱ) at an integer `n`,
defined as ... ⟶ Cⁿ⁻² ⟶ Cⁿ⁻¹ ⟶ ker(d : Cⁿ ⟶ Cⁿ⁺¹) ⟶ 0 ⟶ 0 ⟶ ..., with the kernel
in degree `n`. -/
def truncation (C : cochain_complex 𝓐 ℤ) (n : ℤ) : cochain_complex 𝓐 ℤ :=
{ X := λ i, if i < n
    then C.X i
    else if i = n
      then kernel (C.d n (n+1))
      else 0,
  d := λ i j, if hi : i + 1 = j -- (complex_shape.up ℤ).rel i j
    then if hj : j < n
      then eq_to_hom (by rw if_pos (lt_trans (show i < j, by linarith) hj)) ≫ C.d i j ≫ eq_to_hom (by rw if_pos hj)
      else if hj_eq : j = n
        then eq_to_hom (by rw if_pos (show i < n, by linarith)) ≫
          eq_to_hom (by rw (show i = n - 1, by linarith)) ≫
          (kernel.lift (C.d n (n+1)) (C.d (n-1) n) (C.d_comp_d (n-1) n (n+1)) : C.X (n-1) ⟶ kernel (C.d n (n+1))) ≫
          eq_to_hom (by rw [if_neg hj, if_pos hj_eq])
        else 0
    else 0,
  shape' := λ i j, begin
    rintro h : ¬ (i + 1) = j,
    rw dif_neg h,
  end,
  d_comp_d' := λ i j k, begin
    rintro (rfl : i + 1 = j) (rfl : i + 1 + 1 = k),
    rw dif_pos rfl,
    by_cases hin : i + 1 < n,
    { rw dif_pos hin,
      rw dif_pos rfl,
      by_cases hin' : i + 1 + 1 < n,
      { rw dif_pos hin',
        simp only [category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp,
          homological_complex.d_comp_d_assoc, zero_comp, comp_zero], },
      { rw dif_neg hin',
        have hn : n = i + 1 + 1, linarith,
        subst hn,
        rw dif_pos rfl,
        simp only [eq_to_hom_trans_assoc, category.assoc, preadditive.is_iso.comp_left_eq_zero],
        rw [← category.assoc, ← category.assoc, imker.comp_mono_zero_iff],
        ext,
        simp, } },
    { rw dif_neg hin,
      by_cases hn : i + 1 = n,
      { rw [dif_pos hn, dif_pos rfl, dif_neg (show ¬ i + 1 + 1 < n, by linarith),
          dif_neg (show ¬ i + 1 + 1 = n, by linarith), comp_zero], },
      { rw [dif_neg hn, zero_comp], } },
  end }

namespace truncation

@[reducible] def X_iso_of_lt {i n : ℤ} (h : i < n) : (C.truncation n).X i ≅ C.X i :=
eq_to_iso (by simp [truncation, if_pos h] )

-- don't know whether to go for kernel of d_n or of d_i!
@[reducible] def X_iso_of_eq {i n : ℤ} (h : i = n) : (C.truncation n).X i ≅ kernel (C.d n (n+1)) :=
eq_to_iso (by subst h; simp [truncation, if_neg (show ¬ i < i, by linarith)] )

@[reducible] def X_iso_of_eq' {i n : ℤ} (h : i = n) : (C.truncation n).X i ≅ kernel (C.d i (i+1)) :=
eq_to_iso (by subst h; simp [truncation, if_neg (show ¬ i < i, by linarith)] )

lemma is_zero_X_of_lt {i n : ℤ} (h : n < i) : is_zero ((C.truncation n).X i) :=
begin
  simp [truncation, if_neg (show ¬ i < n, by linarith), if_neg (show ¬ i = n, by linarith),
    is_zero_zero],
end

lemma bounded_by (n : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.truncation n)).bounded_by (n+1) :=
begin
  intros i hi,
  dsimp only [homotopy_category.quotient_obj_as, truncation],
  rw [if_neg, if_neg],
  { apply is_zero_zero, },
  { linarith },
  { linarith }
end

instance is_bounded_above (n : ℤ) :
  ((homotopy_category.quotient _ _).obj (C.truncation n)).is_bounded_above :=
⟨⟨n+1, bounded_by C n⟩⟩

def ι (n : ℤ) : C.truncation n ⟶ C :=
{ f := λ i, if hin : i < n
    then (X_iso_of_lt C hin).hom
    else if hi : i = n
      then (X_iso_of_eq C hi).hom ≫ kernel.ι _ ≫ eq_to_hom (by rw hi)
      else 0,
  comm' := λ i j, begin
    rintro (rfl : i + 1 = j),
    dsimp only [truncation],
    simp only [eq_self_iff_true, eq_to_hom_trans_assoc, dif_pos],
    by_cases hiltn : i < n,
    { rw dif_pos hiltn,
      by_cases hi1ltn : i + 1 < n,
      { rw [dif_pos hi1ltn, dif_pos hi1ltn],
        simp,
        refl, },
      { have hn : i + 1 = n, linarith,
        subst hn,
        rw [dif_neg hi1ltn, dif_neg hi1ltn],
        rw [dif_pos rfl, dif_pos rfl ],
        simp only [eq_to_iso.hom, eq_to_hom_refl, category.comp_id, category.assoc,
          eq_to_hom_trans_assoc, category.id_comp, kernel.lift_ι],
        congr'; linarith, } },
    { rw dif_neg hiltn,
      by_cases hin : i = n,
      { subst hin,
        simp, },
      { rw dif_neg hin,
        rw dif_neg (show ¬ i + 1 < n, by linarith),
        rw dif_neg (show ¬ i + 1 = n, by linarith),
        simp, } },
  end }

def ι_inv (n : ℤ) (hn : is_zero (C.X (n + 1))) : C ⟶ C.truncation n :=
{ f := λ i, if hin : i < n
    then (X_iso_of_lt C hin).inv
    else if hi : i = n
      then (eq_to_hom (by rw hi) : C.X i ⟶ C.X n) ≫
        kernel.lift (C.d n (n+1)) (𝟙 (C.X n)) (hn.eq_zero_of_tgt _) ≫
        (X_iso_of_eq C hi).inv
      else 0,
  comm' := λ i j, begin
    rintro (rfl : i + 1 = j),
    dsimp only [truncation],
    simp only [eq_self_iff_true, eq_to_iso.inv, eq_to_hom_trans_assoc, dif_pos],
    by_cases hiltn : i < n,
    { rw dif_pos hiltn,
      by_cases hi1ltn : i + 1 < n,
      { simp [dif_pos hi1ltn], },
      { have hi1n : i + 1 = n, linarith,
        subst hi1n,
        simp only [eq_self_iff_true, add_left_inj, lt_self_iff_false, not_false_iff, dif_pos,
          dif_neg, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp, ← category.assoc],
        congr' 1,
        ext,
        simp, } },
    { rw dif_neg hiltn,
      by_cases hin : i = n,
      { simp [hin], },
      { rw [dif_neg hin, zero_comp],
        rw dif_neg (show ¬ i + 1 < n, by linarith),
        rw [dif_neg (show ¬ i + 1 = n, by linarith), comp_zero], }, },
  end }

lemma ι_iso (n : ℤ) (hC : ((homotopy_category.quotient _ _).obj C).bounded_by (n+1)) :
  is_iso (truncation.ι C n) :=
{ out := ⟨ι_inv C n (hC (n+1) (by refl)),
  by {
    ext i,
    simp only [homological_complex.comp_f, homological_complex.id_f, ι, ι_inv, eq_to_iso.hom,
      eq_to_iso.inv],
    by_cases hiltn : i < n,
    { simp [dif_pos hiltn], },
    { rw [dif_neg hiltn, dif_neg hiltn],
      by_cases hin : i = n,
      { subst hin,
        simp only [eq_self_iff_true, eq_to_hom_refl, dif_pos, category.id_comp, category.assoc],
        rw ← category.assoc (kernel.ι (C.d i (i + 1))),
        suffices : kernel.ι (C.d i (i + 1)) ≫ kernel.lift (C.d i (i + 1)) (𝟙 (C.X i)) _ = 𝟙 _,
        { simp [this] },
        { ext,
          simp },
        { apply is_zero.eq_zero_of_tgt,
          simpa using hC (i + 1) (by refl), } },
      { apply is_zero.eq_of_tgt,
        apply is_zero_X_of_lt,
        push_neg at hiltn,
        obtain (h1 | h2) := lt_or_eq_of_le hiltn,
        { exact h1 },
        { exact (hin h2.symm).elim, } } } },
  begin
    ext i,
    simp only [ι, ι_inv, eq_to_iso.inv, eq_to_iso.hom, homological_complex.comp_f,
      homological_complex.id_f],
        by_cases hiltn : i < n,
    { simp [dif_pos hiltn], },
    { rw [dif_neg hiltn, dif_neg hiltn],
      by_cases hin : i = n,
      { subst hin,
        simp only [eq_to_hom_refl, category.id_comp, dif_pos, category.comp_id, category.assoc,
          eq_to_hom_trans_assoc, kernel.lift_ι], },
      { apply is_zero.eq_of_tgt,
        simpa using hC i _,
        push_neg at hiltn,
        obtain (h1 | h2) := lt_or_eq_of_le hiltn,
        { exact int.add_one_le_iff.mpr h1, },
        { exact (hin h2.symm).elim, } } }
  end⟩ }

-- feel free to skip this, and directly provide a defn for `ι_succ` below
def map_of_le (m n : ℤ) (h : m ≤ n) : C.truncation m ⟶ C.truncation n :=
{ f := λ i, if him : i < m
    then (X_iso_of_lt C him).hom ≫
      (X_iso_of_lt C (lt_of_lt_of_le him h)).inv -- id
    else if him' : i = m -- domain is ker(d)
      then if hin : i < n
        then (X_iso_of_eq C him').hom ≫ kernel.ι _ ≫
          (eq_to_hom (by rw him') : C.X m ⟶ C.X i) ≫ (X_iso_of_lt C hin).inv -- kernel.ι
        else (X_iso_of_eq' C him').hom ≫ (X_iso_of_eq' C (by linarith : i = n)).inv -- identity
      else 0,
  comm' := λ i j, begin
    rintro (rfl : _ = _),
    delta truncation,
    dsimp only [zero_add, neg_zero, add_zero, zero_lt_one, neg_neg, neg_eq_zero, homological_complex.d_comp_d, dif_neg, dif_pos,
  category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp, homological_complex.d_comp_d_assoc,
  zero_comp, comp_zero, preadditive.is_iso.comp_left_eq_zero, imker.comp_mono_zero_iff,
  homological_complex.d_comp_eq_to_hom, add_tsub_cancel_right, complex_shape.up_rel, add_left_inj, eq_self_iff_true,
  equalizer_as_kernel, kernel.lift_ι, mul_one],
    simp only [eq_self_iff_true, eq_to_iso.hom, eq_to_iso.inv, eq_to_hom_trans, eq_to_hom_trans_assoc, dif_pos],
    by_cases him : i < m,
    { rw dif_pos him,
      by_cases hi1n : i + 1 < n,
      { rw dif_pos hi1n,
        by_cases hi1m : i + 1 < m,
        { simp [dif_pos hi1m], },
        { have hm : i + 1 = m, linarith,
          subst hm,
          rw [dif_neg hi1m, dif_pos rfl, dif_neg hi1m, dif_pos rfl, dif_pos hi1n],
          simp only [eq_to_hom_trans_assoc, category.assoc, eq_to_hom_refl, category.id_comp, kernel.lift_ι_assoc],
          congr';
          ring,
        }
      },
      { rw dif_neg hi1n,
        have hn : i + 1 = n, linarith,
        subst hn,
        have hm : m = i + 1, linarith,
        subst hm,
        simp, } },
    { rw dif_neg him,
      by_cases hm : i = m,
      { subst hm,
        rw [dif_pos rfl, dif_neg (show ¬ (i + 1) < i, by linarith),
          dif_neg (show ¬ i + 1 = i, by linarith), zero_comp],
        obtain (hn | rfl) := lt_or_eq_of_le h,
        { rw dif_pos hn,
          by_cases hi1n : i + 1 < n,
          { rw dif_pos hi1n,
            simp, },
          { rw dif_neg hi1n,
            have hn2 : i + 1 = n, linarith,
            subst hn2,
            simp,
            have hi : eq_to_hom _ ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d (i + 1 - 1) (i + 1)) _ = kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) _,
            { ext, simp, },
            rw [← category.assoc (eq_to_hom _), hi],
            swap, apply C.d_comp_d,
            rw ← category.assoc,
            convert zero_comp,
            ext, simp, } },
        { rw [dif_neg him, dif_neg (show ¬ i + 1 < i, by linarith),
            dif_neg (show i + 1 ≠ i, by linarith), comp_zero], }
      },
      { rw [dif_neg hm, zero_comp, dif_neg (show ¬ i + 1 < m, by linarith),
          dif_neg (show i + 1 ≠ m, by linarith), zero_comp],
      } }
  end }
.

def ι_succ (n : ℤ) : C.truncation n ⟶ C.truncation (n+1) :=
truncation.map_of_le _ _ _ $ by simp only [le_add_iff_nonneg_right, zero_le_one]

--move
lemma _root_.homological_complex.d_from_eq_d_comp_X_next_iso_inv {ι V : Type*} [category V]
  [has_zero_morphisms V] {c : complex_shape ι} (C : homological_complex V c) [has_zero_object V]
    {i j : ι} (r : c.rel i j) :
  C.d_from i = C.d i j ≫ (C.X_next_iso r).inv :=
by simp [C.d_from_eq r]

-- example (A B : 𝓐) (f g : A ⟶ B) (h : f = g) :
--   (category_theory.eq_to_hom (by rw h) : image f ⟶ image g) = (image.eq_to_iso h).hom :=
-- begin
--   sorry -- :-(
-- end

-- lemma factor_thru_image_comp_iso (A B : 𝓐) (f g : A ⟶ B) (h : f = g) :
--   factor_thru_image f ≫ (eq_to_hom (by rw h) : image f ⟶ image g) =
--   factor_thru_image g :=
-- begin
--   sorry
-- end

-- lemma factor_thru_image_comp_iso_comp_image_ι (A B : 𝓐) (f g : A ⟶ B) (h : f = g) :
--   factor_thru_image f ≫ (eq_to_hom (by rw h) : image f ⟶ image g) ≫ image.ι g = f :=
-- begin
--   simp only [iso_comp_image_ι, image.fac],
-- end
-- #exit
--factor_thru_image (e.hom ≫ d) ≫ image.ι (e.hom ≫ d) = factor_thru_image

attribute [reassoc] image.eq_fac

#check image.eq_fac_assoc

def to_imker (n : ℤ) : C.truncation n ⟶ imker C n :=
{ f := λ i, if hi : i = n - 1
           then (X_iso_of_lt C (show i < n, by linarith)).hom ≫ eq_to_hom (by rw hi) ≫
           factor_thru_image (C.d (n-1) n) ≫
           (image.eq_to_iso (by { rw ← C.X_prev_iso_comp_d_to, show (n - 1) + 1 = n, ring, })).hom ≫
             image.pre_comp (C.X_prev_iso (show (n - 1) + 1 = n, by ring)).inv (C.d_to n) ≫
             (imker.X_iso_image_of_eq C hi).inv -- C(n-1) ⟶ Im(d^{n-1})
           else if hn : i = n
             then (X_iso_of_eq C hn).hom ≫
             kernel.lift (C.d n (n+1) ≫ (C.X_next_iso (show n + 1 = n + 1, from rfl)).inv) (kernel.ι _) (by {rw [← category.assoc, kernel.condition, zero_comp]}) ≫
             eq_to_hom begin simp_rw ← C.d_from_eq_d_comp_X_next_iso_inv, end ≫
             (imker.kernel_iso_X_of_eq C hn).hom
             else 0,
  comm' := λ i j, begin
    rintro (rfl : _ = _),
    by_cases hi : i = n - 1,
    { rw dif_pos hi,
      subst hi,
      delta imker truncation, dsimp only,
      rw dif_pos rfl,
      rw dif_pos (show n - 1 + 1 = n, by ring),
      rw dif_pos rfl,
      rw dif_neg (show ¬ n - 1 + 1 < n, by linarith),
      rw dif_pos (show n - 1 + 1 = n, by ring),
      rw dif_neg (show n - 1 + 1 ≠ n - 1, by linarith),
      rw dif_pos (show n - 1 + 1 = n, by ring),
      simp only [← category.assoc],
      congr' 1,
      ext,
      delta image_to_kernel',
      simp only [category.assoc, eq_to_iso.hom, eq_to_hom_refl, category.comp_id, imker.X_iso_image_of_eq_inv, eq_to_hom_trans,
  equalizer_as_kernel, kernel.lift_ι, image.pre_comp_ι],
      congr' 1,
      have foo := (category_theory.limits.image.eq_fac (C.X_prev_iso_comp_d_to (show (n - 1) + 1 = n, by ring)).symm).symm,
      dsimp, dsimp at foo,
      rw foo,
      rw image.fac,
      --simp only [← category_theory.limits.image.eq_fac_assoc (C.X_prev_iso_comp_d_to (show (n - 1) + 1 = n, by ring))],
      sorry,
      /-
      ⊢ factor_thru_image (C.d (n - 1) n) ≫
            eq_to_hom _ ≫ image.ι ((homological_complex.X_prev_iso C _).inv ≫ homological_complex.d_to C n) =
          kernel.lift (C.d n (n + 1)) (C.d (n - 1) n) _ ≫
            kernel.lift (C.d n (n + 1) ≫ (homological_complex.X_next_iso C _).inv) (kernel.ι (C.d n (n + 1))) _ ≫
              eq_to_hom _ ≫ kernel.ι (homological_complex.d_from C n)

C(n-1)->im(d(n-1))->im(previsoinv>>d_to)->C(n)
C(n-1)->ker(d(n))->ker(d(n)>>nextisoinv)->ker(d_from)->C(n)
      -/

      --simp,sorry
    },
    {
      sorry
    }
  end }

lemma short_exact_ι_succ_to_imker (i : ℤ) :
  ∀ n, short_exact ((ι_succ C i).f n) ((to_imker C (i+1)).f n) :=
sorry

example (X Y Z : 𝓐) (g : Z ⟶ X) (h : Y ⟶ Z) : image (h ≫ g) ⟶ image g :=
image.pre_comp h g

end truncation

end cochain_complex
