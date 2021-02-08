import data.finset.lattice

variables {α : Type*} [linear_order α]

-- Both lemmas (and `min'` versions) PR'd as https://github.com/leanprover-community/mathlib/pull/6089

lemma finset.max'_subset {s t : finset α} (H : s.nonempty) (hst : s ⊆ t) :
  s.max' H ≤ t.max' (H.mono hst) :=
finset.le_max' _ _ (hst (s.max'_mem H))

lemma finset.max'_insert (a : α) (s : finset α) (H : s.nonempty) :
  (insert a s).max' (s.insert_nonempty a) = max (s.max' H) a :=
begin
  apply eq_max,
  { exact finset.max'_subset _ (s.subset_insert a) },
  { exact (insert a s).le_max' _ (s.mem_insert_self a) },
  { intros b hsb hab,
    apply finset.max'_le,
    intros c hc,
    rcases finset.mem_insert.mp hc with (rfl | hcs),
    { exact hab },
    { exact le_trans (s.le_max' _ hcs) hsb } },
end
