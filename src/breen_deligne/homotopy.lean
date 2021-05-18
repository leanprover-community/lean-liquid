import algebra.homology.homotopy

import for_mathlib.homotopy

import breen_deligne.category
import breen_deligne.suitable

namespace breen_deligne

open category_theory category_theory.limits free_abelian_group homological_complex FreeMat

open_locale big_operators nnreal zero_object

namespace data

variables (BD : data)


-- generalize this to something like `functor.map_homotopy`
@[simps]
def homotopy_two_mul {BD₁ BD₂ : data} {f g : BD₁ ⟶ BD₂} (h : homotopy f g) :
  homotopy ((mul 2).map f) ((mul 2).map g) :=
{ hom := λ j i, universal_map.mul 2 (h.hom j i),
  zero' := λ i j hij, by rw [h.zero i j hij, add_monoid_hom.map_zero],
  comm :=
  begin
    intro j,
    simp only [mul_map_f, h.comm j, add_monoid_hom.map_add],
    dsimp [d_next, prev_d],
    rcases (complex_shape.down ℕ).next j with _|⟨k,hk⟩;
    rcases (complex_shape.down ℕ).prev j with _|⟨i,hi⟩;
    dsimp [d_next, prev_d];
    simp only [add_zero, zero_add, add_monoid_hom.map_zero];
    repeat { erw [universal_map.mul_comp] };
    refl
  end }

def homotopy_pow' (h : homotopy (BD.proj 2) (BD.sum 2)) :
  Π N, homotopy (hom_pow' (BD.proj 2) N) (hom_pow' (BD.sum 2) N)
| 0     := homotopy.refl _
| (N+1) := (homotopy_two_mul (homotopy_pow' N)).comp h

def homotopy_mul (h : homotopy (BD.proj 2) (BD.sum 2)) (N : ℕ) :
  homotopy (BD.proj (2^N)) (BD.sum (2^N)) :=
(homotopy.of_eq (BD.hom_pow'_proj N).symm).trans $
  ((BD.homotopy_pow' h N).comp_left (BD.pow'_iso_mul N).inv).trans $
  (homotopy.of_eq $ BD.hom_pow'_sum N)

end data

/-- A Breen--Deligne `package` consists of Breen--Deligne `data`
that forms a complex, together with a `homotopy`
between the two universal maps `σ_add` and `σ_proj`. -/
structure package :=
(data       : data)
(homotopy   : homotopy (data.proj 2) (data.sum 2))

namespace package

class adept (BD : out_param package) (c_ : out_param $ ℕ → ℝ≥0) (c' : ℕ → ℝ≥0) : Prop :=
(htpy_suitable' :
  ∀ i, (BD.homotopy.hom i (i+1)).suitable (rescale_constants c_ 2 i) (c' (i+1) * c_ (i+1)))

instance adept.htpy_suitable (BD : package) (c_ c' : ℕ → ℝ≥0) [adept BD c_ c'] (j i : ℕ) :
  (BD.homotopy.hom j i).suitable (rescale_constants c_ 2 j) (c' i * c_ i) :=
begin
  by_cases hij : j + 1 = i,
  { rw ← hij, apply adept.htpy_suitable' },
  { rw BD.homotopy.zero,
    { apply_instance },
    { exact hij } }
end

namespace adept

open category_theory

variables (BD : package) (c_ c' : ℕ → ℝ≥0) [adept BD c_ c']

-- instance mul_adept_suitable (N : ℕ) (f : (data.mul N).obj BD.data ⟶ BD.data) (i : ℕ) (c₁ : ℝ≥0)
--   [hf : universal_map.suitable c₁ (c_ i) (f.f i)] :
--   universal_map.suitable c₁ ((c' * c_) i) (f.f i) :=
-- begin
--   refine hf.le _ _ _ _ le_rfl _,
--   dsimp,
--   apply fact.out
-- end

instance homotopy_pow'_suitable (j i : ℕ) :
  Π N, ((BD.data.homotopy_pow' BD.homotopy N).hom j i).suitable
    (rescale_constants c_ (2 ^ N) j) ((c' * c_) i)
| 0     := universal_map.suitable_zero _ _
| (N+1) :=
begin
  dsimp [data.homotopy_pow'],
  refine @universal_map.suitable_add _ _ _ _ _ _ (id _) (id _),
  { refine @universal_map.suitable.comp
      _ _ _ _ _ _ (c' i * c_ i) _ _ (id _),
    refine @universal_map.mul_suitable _ _ _ _ _ (id _) _ _,
    refine (homotopy_pow'_suitable N).le _ _ _ _ _ le_rfl,
    calc rescale_constants c_ (2 ^ (N + 1)) j
        = c_ j * (2⁻¹ * (2 ^ N)⁻¹) : by simp only [rescale_constants, pow_succ, mul_inv']
    ... ≤ c_ j * (1 * (2 ^ N)⁻¹)   : mul_le_mul' le_rfl (mul_le_mul' (by norm_num) le_rfl)
    ... = c_ j * (2 ^ N)⁻¹         : by rw one_mul, },
  { refine @universal_map.suitable.comp
      _ _ _ _ _ _ (rescale_constants c_ 2 j) _ _ (id _),
    refine @universal_map.mul_suitable _ _ _ _ _ (id _) 2 ⟨zero_lt_two⟩,
    simp only [rescale_constants, pow_succ, mul_inv'],
    rw [← mul_assoc, mul_right_comm],
    exact @universal_map.suitable_mul_right _ _ _ _ _ _ _ }
end
.

-- move to mathlib
attribute [simps] homotopy.refl homotopy.symm homotopy.trans homotopy.comp_left homotopy.comp_right

instance homotopy_mul_suitable (j i N : ℕ) :
  ((BD.data.homotopy_mul BD.homotopy N).hom j i).suitable
    (rescale_constants c_ (2 ^ N) j) ((c' * c_) i) :=
begin
  dsimp [data.homotopy_mul, homotopy.trans_hom],
  simp only [add_zero, zero_add],
  refine @universal_map.suitable.comp _ _ _ _ _ _ (rescale_constants c_ (2 ^ N) j) _ _ (id _),
  generalize : (rescale_constants c_ (2 ^ N) j) = c,
  induction N with N IH,
  { dsimp [data.pow'_iso_mul, data.mul_one_iso, FreeMat.one_mul_iso],
    -- jmc: I don't understand why TC doesn't find the following instance...
    exact @universal_map.suitable_of _ _ _ _ _ (basic_universal_map.one_mul_hom_suitable _), },
  { dsimp [data.pow'_iso_mul],
    resetI,
    refine @universal_map.suitable.comp _ _ _ _ _ _ c _ (id _) (id _),
    { apply_instance },
    { dsimp [data.mul_mul_iso, FreeMat.mul_mul_iso],
      erw [nat_iso.of_components.inv_app, FreeMat.iso_mk'_inv],
      apply_instance } }
end

end adept

end package

end breen_deligne
