import topology.separation
import topology.locally_constant.basic

/-
**TODO**: In mathlib, rename is_closed_inter to isclosed.inter and same with is_clopen
to allow dot notation.
-/

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

end set

open set topological_space
open_locale topological_space

section
variables {α : Type*} [topological_space α]

lemma is_clopen_Union {β : Type*} [fintype β] {s : β → set α}
  (h : ∀ i, is_clopen (s i)) : is_clopen (⋃ i, s i) :=
⟨(is_open_Union (forall_and_distrib.1 h).1), (is_closed_Union (forall_and_distrib.1 h).2)⟩

lemma is_clopen_bUnion {β : Type*} {s : finset β} {f : β → set α} (h : ∀i∈s, is_clopen (f i)) :
  is_clopen (⋃i∈s, f i) :=
⟨is_open_bUnion (λ i hi, (h i hi).1),
 by {show is_closed (⋃ (i : β) (H : i ∈ (↑s : set β)), f i), rw bUnion_eq_Union,
    apply is_closed_Union, rintro ⟨i, hi⟩, exact (h i hi).2}⟩

end


variables {X : Type*} [topological_space X]

lemma exists_open_set_nhds {s U : set X} (h : ∀ x ∈ s, U ∈ 𝓝 x) :
  ∃ V : set X, s ⊆ V ∧ is_open V ∧ V ⊆ U :=
begin
  have := λ x hx, (nhds_basis_opens x).mem_iff.1 (h x hx),
  choose! Z hZ hZ'  using this,
  refine ⟨⋃ x ∈ s, Z x, _, _, bUnion_subset hZ'⟩,
  { intros x hx,
    simp only [mem_Union],
    exact ⟨x, hx, (hZ x hx).1⟩ },
  { apply is_open_Union,
    intros x,
    by_cases hx : x ∈ s ; simp [hx],
    exact (hZ x hx).2 }
end

lemma toto {ι : Type*} [nonempty ι] {V : ι → set X} (hV : directed (⊇) V)
  (hV_cpct : ∀ i, is_compact (V i)) (hV_closed : ∀ i, is_closed (V i))
  {U : set X} (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) :
  ∃ i, V i ⊆ U :=
begin
  set Y := ⋂ i, V i,
  obtain ⟨W, hsubW, W_op, hWU⟩ : ∃ W, Y ⊆ W ∧ is_open W ∧ W ⊆ U,
    from exists_open_set_nhds hU,
  suffices : ∃ i, V i ⊆ W,
  { rcases this with ⟨i, hi⟩,
    refine ⟨i, set.subset.trans hi hWU⟩ },
  by_contradiction H,
  push_neg at H,
  replace H : ∀ i, (V i ∩ Wᶜ).nonempty := λ i, set.inter_compl_nonempty_iff.mpr (H i),
  have : (⋂ i, V i ∩ Wᶜ).nonempty,
  { apply is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _ _ H,
    { intro i,
      exact (hV_cpct i).inter_right W_op.is_closed_compl },
    { intro i,
      apply is_closed_inter (hV_closed i) W_op.is_closed_compl },
    { intros i j,
      rcases hV i j with ⟨k, hki, hkj⟩,
      use k,
      split ; intro x ; simp only [and_imp, mem_inter_eq, mem_compl_eq] ; tauto  } },
  have : ¬ (⋂ (i : ι), V i) ⊆ W,
    by simpa [← Inter_inter, inter_compl_nonempty_iff],
  contradiction,
end

lemma toto' [compact_space X] {ι : Type*} [nonempty ι] {V : ι → set X} (hV : directed (⊇) V)
  (hV_closed : ∀ i, is_closed (V i))
  {U : set X} (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) :
  ∃ i, V i ⊆ U :=
toto hV (λ i, (hV_closed i).compact) hV_closed hU

section
variables [compact_space X] [t2_space X] [totally_disconnected_space X]

lemma nhds_basis_clopen (x : X) : (𝓝 x).has_basis (λ s : set X, x ∈ s ∧ is_clopen s) id :=
⟨λ U, begin
  split,
  { have : connected_component x = {x},
      from totally_disconnected_space_iff_connected_component_singleton.mp ‹_› x,
    rw connected_component_eq_Inter_clopen at this,
    intros hU,
    let N := {Z // is_clopen Z ∧ x ∈ Z},
    suffices : ∃ Z : N, Z.val ⊆ U,
    { rcases this with ⟨⟨s, hs, hs'⟩, hs''⟩,
      exact ⟨s, ⟨hs', hs⟩, hs''⟩ },
    haveI : nonempty N := ⟨⟨univ, is_clopen_univ, mem_univ x⟩⟩,
    have hNcl : ∀ Z : N, is_closed Z.val := (λ Z, Z.property.1.2),
    have hdir : directed superset (λ Z : N, Z.val),
    { rintros ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩,
    exact ⟨⟨s ∩ t, is_clopen_inter hs ht, ⟨hxs, hxt⟩⟩, inter_subset_left s t, inter_subset_right s t⟩ },
    have h_nhd: ∀ y ∈ (⋂ Z : N, Z.val), U ∈ 𝓝 y,
    { intros y y_in,
      erw [this, mem_singleton_iff] at y_in,
      rwa y_in },
    exact toto' hdir hNcl h_nhd },
  { rintro ⟨V, ⟨hxV, V_op, -⟩, hUV : V ⊆ U⟩,
    rw mem_nhds_sets_iff,
    exact ⟨V, hUV, V_op, hxV⟩ }
end⟩

lemma is_topological_basis_clopen : is_topological_basis {s : set X | is_clopen s} :=
begin
  apply is_topological_basis_of_open_of_nhds (λ U (hU : is_clopen U), hU.1),
  intros x U hxU U_op,
  have : U ∈ 𝓝 x,
  from mem_nhds_sets U_op hxU,
  rcases (nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V ⊆ U⟩,
  use V,
  tauto
end
end

variables [compact_space X]
  {Y : Type*} [topological_space Y] [t2_space Y] [compact_space Y] [totally_disconnected_space Y]

lemma embedding.preimage_clopen {f : X → Y} (hf : embedding f) {U : set X} (hU : is_clopen U) :
  ∃ V : set Y, is_clopen V ∧ U = f ⁻¹' V :=
begin
  cases hU with hU hU',
  have hfU : is_compact (f '' U),
    from hU'.compact.image hf.continuous,
  obtain ⟨W, W_op, hfW⟩ : ∃ W : set Y, is_open W ∧ f ⁻¹' W = U,
  { rw hf.to_inducing.induced at hU,
    exact is_open_induced_iff.mp hU },
  obtain ⟨ι, Z : ι → set Y, hWZ : W = ⋃ i, Z i, hZ : ∀ i, is_clopen $ Z i⟩ :=
    is_topological_basis_clopen.open_eq_Union W_op,
  have : f '' U ⊆ ⋃ i, Z i,
  { rw [image_subset_iff, ← hWZ, hfW] },
  obtain ⟨I, hI⟩ : ∃ I : finset ι, f '' U ⊆ ⋃ i ∈ I, Z i,
    from hfU.elim_finite_subcover _ (λ i, (hZ i).1) this,
  refine ⟨⋃ i ∈ I, Z i, _, _⟩,
  { apply is_clopen_bUnion,
    tauto },
  { apply subset.antisymm,
    exact image_subset_iff.mp hI,
    have : (⋃ i ∈ I, Z i) ⊆ ⋃ i, Z i,
      from bUnion_subset_Union _ _,
    rw [← hfW, hWZ],
    mono },
end
