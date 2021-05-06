import data.set.lattice


namespace set -- Next two lemmas are not needed in the end, but still missing from mathlib

lemma bInter_inter {ι α : Type*} {s : set ι} (hs : s.nonempty) (f : ι → set α) (t : set α) :
(⋂ i ∈ s, f i ∩ t) = (⋂ i ∈ s, f i) ∩ t :=
begin
  haveI : nonempty s := hs.to_subtype,
  simp [bInter_eq_Inter, ← Inter_inter]
end

lemma inter_bInter {ι α : Type*} {s : set ι} (hs : s.nonempty) (f : ι → set α) (t : set α) :
(⋂ i ∈ s, t ∩ f i) = t ∩ ⋂ i ∈ s, f i :=
begin
  rw [inter_comm, ← bInter_inter hs],
  simp [inter_comm]
end

lemma Union_prop {ι α : Type*} (f : ι → set α) (p : ι → Prop) (i : ι) [decidable $ p i] :
  (⋃ (h : p i), f i) = if p i then f i else ∅ :=
begin
  ext x,
  rw mem_Union,
  split_ifs ; tauto,
end

@[simp]
lemma Union_prop_pos {ι α : Type*} {p : ι → Prop} {i : ι} (hi : p i) (f : ι → set α)  :
  (⋃ (h : p i), f i) = f i :=
begin
  classical,
  ext x,
  rw [Union_prop, if_pos hi]
end

@[simp]
lemma Union_prop_neg {ι α : Type*} {p : ι → Prop} {i : ι} (hi : ¬ p i) (f : ι → set α)  :
  (⋃ (h : p i), f i) = ∅ :=
begin
  classical,
  ext x,
  rw [Union_prop, if_neg hi]
end

lemma mem_bUnion_iff' {ι α : Type*} (f : ι → set α) (p : ι → Prop) [decidable_pred p] {x : α} :
  x ∈ (⋃ i (h : p i), f i) ↔ ∃ i (h : p i), x ∈ f i :=
mem_bUnion_iff


end set
