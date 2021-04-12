import breen_deligne.category

namespace breen_deligne

namespace eg

/-!

# An explicit nontrivial example of Breen-Deligne data

This example is explained in Definition 1.10 of
the blueprint https://leanprover-community.github.io/liquid/ .

-/

open universal_map

/-- The `i`-th rank of this BD package is `2^i`. -/
def rank : ℕ → FreeMat
| 0     := 1
| (n+1) := rank n + rank n

lemma rank_eq : ∀ n, rank n = 2 ^ n
| 0     := rfl
| (n+1) := by rw [pow_succ, two_mul, rank, rank_eq]

def σπ (n : ℕ) := σ n - π n

lemma σπ_comp_double {m n} (f : universal_map m n) :
  comp (σπ n) (double f) = comp f (σπ m) :=
by simp only [σπ, add_monoid_hom.map_sub, add_monoid_hom.sub_apply, σ_comp_double, π_comp_double]

/-- The `i`-th map of this BD package is inductively defined
as the simplest solution to the homotopy condition,
so that the homotopy will consist of identity maps. -/
def map : Π n, rank (n+1) ⟶ rank n
| 0     := σπ 1
| (n+1) := (σπ (rank (n+1))) - (map n).double

lemma is_complex_zero :
  map 1 ≫ map 0 = 0 :=
show comp (σπ 1) (σπ 2 - double (σπ 1)) = 0,
by rw [add_monoid_hom.map_sub, σπ_comp_double, sub_self]

lemma is_complex_succ (n : ℕ) (ih : (comp (map n)) (map (n + 1)) = 0) :
  comp (map (n+1)) (map (n+1+1)) = 0 :=
begin
  show comp (map (n+1)) ((σπ (rank $ n+1+1)) - double (map (n+1))) = 0,
  simp only [add_monoid_hom.map_sub, ← σπ_comp_double,
    ← add_monoid_hom.sub_apply],
  simp only [← add_monoid_hom.map_sub, map, sub_sub_cancel],
  erw [comp_double_double, ih, double_zero]
end

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
def hmap : Π (j i : ℕ) (h : i = j+1), (BD.double.X j) ⟶ (BD.X i)
| j i rfl := 𝟙 _

def h : homotopy BD.σ BD.π :=
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

/-- An example of a Breen--Deligne data coming from a nontrivial complex. -/
def eg : package := ⟨eg.BD, eg.h⟩

end breen_deligne
