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
  comm' := sorry }

def ι_succ (n : ℤ) : C.truncation n ⟶ C.truncation (n+1) :=
truncation.map_of_le _ _ _ $ by simp only [le_add_iff_nonneg_right, zero_le_one]

def to_imker (n : ℤ) : C.truncation n ⟶ imker C n :=
{ f := λ i, if hi : i = n - 1
           then sorry ≫ factor_thru_image (C.d (n-1) n) ≫ sorry -- C(n-1) ⟶ Im(d^{n-1})
           else if i = n
             then sorry
             else 0,
  comm' := sorry }

lemma short_exact_ι_succ_to_imker (i : ℤ) :
  ∀ n, short_exact ((ι_succ C i).f n) ((to_imker C (i+1)).f n) :=
sorry

end truncation

end cochain_complex
