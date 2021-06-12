import data.setoid.partition

-- PRed in  #7910

import for_mathlib.quotient -- PR together with  this file

open set

lemma setoid.eqv_class_mem' {α : Type*} {c : set (set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {x} :
  {y : α | (setoid.mk_classes c H).rel x y} ∈ c :=
by { convert setoid.eqv_class_mem H, ext, rw setoid.comm }

structure indexed_partition {ι α : Type*} (s : ι → set α) :=
(eq_of_mem : ∀ {x i j}, x ∈ s i → x ∈ s j → i = j)
(some : ι → α)
(some_mem : ∀ i, some i ∈ s i)
(index : α → ι)
(mem_index : ∀ x, x ∈ s (index x))

/-- The non-constructive constructor for `indexed_partition`. -/
noncomputable
def indexed_partition.mk' {ι α : Type*} (s : ι → set α) (dis : ∀ i j, i ≠ j → disjoint (s i) (s j))
(empty : ∀ i, (s i).nonempty) (ex : ∀ x, ∃ i, x ∈ s i) : indexed_partition s :=
{ eq_of_mem := begin
    classical,
    intros x i j hxi hxj,
    by_contra h,
    exact dis _ _ h ⟨hxi, hxj⟩
  end,
  some := λ i, (empty i).some,
  some_mem := λ i, (empty i).some_spec,
  index := λ x, (ex x).some,
  mem_index := λ x, (ex x).some_spec }

namespace indexed_partition
variables {ι α : Type*} {s : ι → set α} (hs : indexed_partition s)
include hs

lemma exists_mem (x : α) : ∃ i, x ∈ s i := ⟨hs.index x, hs.mem_index x⟩

lemma Union : (⋃ i, s i) = univ :=
by { ext x, simp [hs.exists_mem x] }

lemma disjoint : ∀ {i j}, i ≠ j → disjoint (s i) (s j) :=
λ i j h x ⟨hxi, hxj⟩,h (hs.eq_of_mem hxi hxj)

lemma eq_index_of_mem {x i} (hxi : x ∈ s i) : i = hs.index x :=
hs.eq_of_mem hxi (hs.mem_index x)

protected def setoid (hs : indexed_partition s) : setoid α :=
{ r := λ x y, ∃ i, x ∈ s i ∧ y ∈ s i,
  iseqv := ⟨λ x, ⟨hs.index x, hs.mem_index x, hs.mem_index x⟩,
            λ x y ⟨i, hxi, hyi⟩, ⟨i, hyi, hxi⟩,
            λ x y z ⟨i, hxi, hyi⟩ ⟨j, hyj, hzj⟩, ⟨i, hxi, (hs.eq_of_mem hyj hyi) ▸ hzj⟩⟩ }

lemma some_index (x : α) : hs.setoid.rel (hs.some (hs.index x)) x :=
⟨hs.index x, hs.some_mem (hs.index x), hs.mem_index x⟩

protected def quotient := quotient hs.setoid

def proj : α → hs.quotient := @quotient.mk α hs.setoid

lemma proj_eq_iff {x y : α} : hs.proj x = hs.proj y ↔ hs.setoid.rel x y :=
quotient.eq_rel

noncomputable
def out : hs.quotient → α := @quotient.out α hs.setoid

@[simp] lemma proj_out (x : hs.quotient) : hs.proj (hs.out x) = x :=
quot.out_eq _

lemma out_proj (x : α) : hs.setoid.rel (hs.out (hs.proj x)) x :=
quotient.mk_out' x

@[simp] lemma out_proj_some (i : ι) : hs.out (hs.proj (hs.some i)) ∈ s i :=
begin
  letI : setoid α := hs.setoid,
  rcases quotient.mk_out (hs.some i) with ⟨j, hj, hj'⟩,
  rwa hs.eq_of_mem hj' (hs.some_mem i) at hj
end

@[simp] lemma index_out_proj_some (i : ι) : hs.index (hs.out $ hs.proj $ hs.some i) = i :=
hs.eq_of_mem (hs.mem_index $ hs.out $ hs.proj (hs.some i)) (hs.out_proj_some i)

lemma class_of {x : α} : set_of (hs.setoid.rel x) = s (hs.index x) :=
begin
  ext y,
  change (∃ i, x ∈ s i ∧ y ∈ s i) ↔ y ∈ s (hs.index x),
  split,
  { rintros ⟨i, hxi, hyi⟩,
    rwa hs.eq_index_of_mem hxi at hyi },
  { intro h,
    exact ⟨hs.index x, hs.mem_index x, h⟩ },
end

noncomputable
def equiv_quotient : ι ≃ hs.quotient :=
{ to_fun := hs.proj ∘ hs.some,
  inv_fun := hs.index ∘ hs.out,
  left_inv := hs.index_out_proj_some,
  right_inv := begin
    intros z,
    conv_rhs { rw ← hs.proj_out z},
    rw proj_eq_iff,
    apply some_index,
  end }

@[simp] lemma equiv_quotient_index_apply (x : α) : hs.equiv_quotient (hs.index x) = hs.proj x :=
hs.proj_eq_iff.mpr (some_index hs x)

lemma equiv_quotient_index : hs.equiv_quotient ∘ hs.index = hs.proj :=
funext hs.equiv_quotient_index_apply


lemma proj_fiber (x : hs.quotient) : hs.proj ⁻¹' {x} = s (hs.equiv_quotient.symm x) :=
begin
  letI := hs.setoid,
  change {y | ⟦y⟧ = x} = s(hs.index $ hs.out x),
  rw ← hs.class_of,
  ext y,
  change ⟦y⟧ = x ↔ hs.setoid.rel (hs.out x) y,
  rw [hs.setoid.comm, quotient.mk_eq_iff_out],
  refl
end

end indexed_partition
