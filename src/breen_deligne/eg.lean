import breen_deligne.category

namespace breen_deligne

namespace eg
/-! ## An explicit nontrivial example -/

open universal_map

/-- The `i`-th rank of this BD package is `2^i`. -/
def rank : ℕ → ℕ
| 0     := 1
| (n+1) := rank n + rank n

lemma rank_eq : ∀ n, rank n = 2 ^ n
| 0     := rfl
| (n+1) := by rw [pow_succ, two_mul, rank, rank_eq]

/-- The `i`-th map of this BD package is inductively defined
as the simplest solution to the homotopy condition,
so that the homotopy will consist of identity maps. -/
def map : Π n, universal_map (rank (n+1)) (rank n)
| 0     := σ_diff 1
| (n+1) := (σ_diff (rank (n+1))) - (map n).double

/-- The Breen--Deligne data for the example BD package. -/
@[simps]
def data : data := ⟨rank, map⟩

/-- The `n`-th homotopy map for the example BD package is the identity. -/
def hmap (n : ℕ) : universal_map (rank n + rank n) (rank (n+1)) :=
universal_map.id _

lemma hmap_is_homotopy :
  ∀ n, σ_diff (rank (n+1)) =
  comp (map (n+1)) (hmap (n+1)) + comp (hmap n) (map n).double
| _ := by { simp only [hmap, id_comp, comp_id, map], simp only [sub_add_cancel], }

lemma hmap_is_homotopy_zero :
  σ_diff (rank 0) = universal_map.comp (map 0) (hmap 0) :=
begin
  simp only [hmap, id_comp, comp_id, map, σ_diff, σ_add, σ_proj, sub_sub],
  congr' 3;
  { ext (j : fin 1) (i : fin 2),
    fin_cases j, fin_cases i; refl }
end

/-- The homotopy for the example BD package. -/
@[simps]
def homotopy : homotopy data := ⟨hmap, hmap_is_homotopy, hmap_is_homotopy_zero⟩

lemma is_complex_zero :
  comp (map 0) (map 1) = 0 :=
begin
  show comp (σ_diff 1) (σ_diff (1+1) - double (σ_diff 1)) = 0,
  rw [add_monoid_hom.map_sub, σ_diff_comp_double, sub_self],
end

lemma is_complex_succ (n : ℕ) (ih : (comp (map n)) (map (n + 1)) = 0) :
  comp (map (n+1)) (map (n+1+1)) = 0 :=
begin
  have H := hmap_is_homotopy n,
  simp only [hmap, comp_id, id_comp] at H,
  show comp (map (n+1)) ((σ_diff (rank $ n+1+1)) - double (map (n+1))) = 0,
  simp only [add_monoid_hom.map_sub, ← σ_diff_comp_double, H],
  simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply],
  simp only [comp_double_double, ih, double_zero, add_zero, sub_self],
end

lemma is_complex : is_complex data
| 0     := is_complex_zero
| (n+1) := is_complex_succ n (is_complex n)

end eg

/-- An example of a Breen--Deligne data coming from a nontrivial complex. -/
def eg : package := ⟨eg.data, eg.is_complex, eg.homotopy⟩

end breen_deligne
