import topology.separation
import topology.subset_properties

variables {X Y : Type*} [topological_space X] [topological_space Y]

lemma is_totally_disconnected_of_totally_disconnected_space
  [totally_disconnected_space X] (s : set X) :
  is_totally_disconnected s :=
λ t hts ht,
totally_disconnected_space.is_totally_disconnected_univ _ (set.subset_univ t) ht

lemma is_preconnected.subsingleton [totally_disconnected_space X] {s : set X}
  (hs : is_preconnected s) :
  subsingleton s :=
is_totally_disconnected_of_totally_disconnected_space s s (set.subset.refl _) hs

namespace embedding

lemma t2_space [t2_space Y] {f : X → Y} (hf : embedding f) :
  t2_space X :=
{ t2 := λ x y h,
  begin
    obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation (hf.inj.ne h),
    refine ⟨f ⁻¹' U, f ⁻¹' V,
      hf.continuous.is_open_preimage _ hU,
      hf.continuous.is_open_preimage _ hV,
      set.mem_preimage.mpr hx,
      set.mem_preimage.mpr hy, _⟩,
    rw ← set.disjoint_iff_inter_eq_empty at hUV ⊢,
    exact hUV.preimage _
  end }

lemma is_totally_disconnected {f : X → Y} (hf : embedding f)
  (s : set X) (h : is_totally_disconnected (f '' s)) :
  is_totally_disconnected s :=
begin
  rintro t hts ht,
  have htc : is_preconnected (f '' t) := ht.image f hf.continuous.continuous_on,
  haveI := h _ (set.image_subset _ hts) htc,
  constructor,
  intros a b,
  ext,
  apply hf.inj,
  have := @subsingleton.elim (f '' t) _
    ⟨f a, set.mem_image_of_mem f a.2⟩ ⟨f b, set.mem_image_of_mem f b.2⟩,
  simpa only [subtype.mk_eq_mk]
end

lemma totally_disconnected_space [totally_disconnected_space Y] {f : X → Y} (hf : embedding f) :
  totally_disconnected_space X :=
{ is_totally_disconnected_univ :=
  begin
    apply hf.is_totally_disconnected,
    apply is_totally_disconnected_of_totally_disconnected_space
  end }

end embedding

namespace inducing

#check cluster_pt

lemma exists_open {f : X → Y} (hf : inducing f) ⦃U : set X⦄ (hU : is_open U) :
  ∃ V, is_open V ∧ f ⁻¹' V = U :=
begin
  unfreezingI { cases hf.induced },
  rwa ← @is_open_induced_iff X Y _ _ f
end

lemma is_compact {f : X → Y} (hf : inducing f) (s : set X) (hs : is_compact (f '' s)) :
  is_compact s :=
begin
  intros F hF hFs,
  have : (F.map f) ≤ filter.principal (f '' s),
  { rw filter.map_le_iff_le_comap,
    simp only [filter.le_principal_iff, filter.comap_principal] at hFs ⊢,
    apply filter.mem_sets_of_superset hFs,
    exact set.subset_preimage_image f s },
  haveI : (F.map f).ne_bot := _,
  obtain ⟨-, ⟨x, hxs, rfl⟩, hx⟩ := hs this,
  refine ⟨x, hxs, _⟩,
  rw cluster_pt_iff at hx ⊢,
  intros U hU V hV,
  rw [hf.nhds_eq_comap, filter.mem_comap_sets] at hU,
  rcases hU with ⟨U', hU', hfU'⟩,
  specialize hx hU',
  have : f '' V ∈ F.map f,
  { sorry },
  sorry,
  sorry
end

end inducing
