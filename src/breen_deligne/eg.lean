import breen_deligne.suitable

open_locale nnreal

namespace breen_deligne

namespace eg

/-!

# An explicit nontrivial example of Breen-Deligne data

This example is explained in Definition 1.10 of
the blueprint https://leanprover-community.github.io/liquid/ .

-/

open universal_map

/-- The `i`-th rank of this BD package is `2^i`. -/
def rank (i : ℕ) : FreeMat := 2 ^ i

def σπ (n : ℕ) := universal_map.sum n 2 - universal_map.proj n 2

lemma σπ_comp_mul_two {m n} (f : universal_map m n) :
  comp (σπ n) (mul 2 f) = comp f (σπ m) :=
by simp only [σπ, add_monoid_hom.map_sub, add_monoid_hom.sub_apply, sum_comp_mul, proj_comp_mul]

/-- The `i`-th map of this BD package is inductively defined
as the simplest solution to the homotopy condition,
so that the homotopy will consist of identity maps. -/
def map : Π n, rank (n+1) ⟶ rank n
| 0     := σπ 1
| (n+1) := σπ (rank (n+1)) - mul 2 (map n)

lemma map_succ (n : ℕ) : map (n+1) = σπ (rank (n+1)) - mul 2 (map n) := rfl

lemma is_complex_zero : map 1 ≫ map 0 = 0 :=
show comp (σπ 1) (σπ 2 - mul 2 (σπ 1)) = 0,
by { rw [add_monoid_hom.map_sub, σπ_comp_mul_two, sub_eq_zero], refl }

lemma is_complex_succ (n : ℕ) (ih : (comp (map n)) (map (n + 1)) = 0) :
  comp (map (n+1)) (map (n+1+1)) = 0 :=
by rw [map_succ (n+1), add_monoid_hom.map_sub, ← σπ_comp_mul_two, ← add_monoid_hom.sub_apply,
    ← add_monoid_hom.map_sub, map_succ n, sub_sub_cancel, ← mul_comp, ← map_succ, ih,
    add_monoid_hom.map_zero]

/-- The Breen--Deligne data for the example BD package. -/
def BD : data :=
chain_complex.mk' rank map
begin
  intro n,
  induction n with n ih,
  { exact is_complex_zero },
  { exact is_complex_succ n ih }
end

open differential_object differential_object.complex_like
open category_theory category_theory.limits category_theory.preadditive

/-- The `n`-th homotopy map for the example BD package is the identity. -/
def hmap : Π (j i : ℕ) (h : i = j+1), (((data.mul 2).obj BD).X j) ⟶ (BD.X i)
| j i rfl := 𝟙 _

def h : homotopy (BD.sum 2) (BD.proj 2) :=
{ h := λ j i, if h : i = j+1 then hmap j i h else 0,
  h_eq_zero := λ i j h, dif_neg h,
  comm :=
  begin
    intros i j k,
    simp only [htpy_idx_rel₁_ff_nat, htpy_idx_rel₂_ff_nat],
    rintro (rfl|⟨rfl,rfl⟩),
    { rintro rfl,
      rw [dif_pos rfl, dif_pos rfl],
      dsimp [hmap],
      rw [category.id_comp, category.comp_id],
      erw [chain_complex.mk'_d', map, chain_complex.mk'_d', sub_add_cancel],
      refl },
    { rintro ⟨⟩ }
  end }

end eg

/-- An example of a Breen--Deligne package coming from a nontrivial complex. -/
def eg : package := ⟨eg.BD, eg.h⟩

namespace eg

variables (r r' : ℝ≥0)

/-- Very suitable sequence of constants for the example Breen--Deligne package -/
def c_ (r r' : ℝ≥0) : ℕ → ℝ≥0 :=
sorry

instance very_suitable : eg.data.very_suitable r r' (c_ r r') :=
sorry

/-- Adept sequence of constants for the example Breen--Deligne package -/
def c' (c_ : ℕ → ℝ≥0) : ℕ → ℝ≥0 :=
sorry

instance adept (c_ : ℕ → ℝ≥0) : package.adept eg c_ (c' c_) :=
sorry

end eg

end breen_deligne
