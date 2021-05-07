import analysis.normed_space.normed_group_hom
import topology.algebra.normed_group

import for_mathlib.normed_group

noncomputable theory

open set normed_group_hom uniform_space


-- #7459
@[to_additive]
lemma subgroup.mem_map_of_mem {G H : Type*} [group G] [group H] {G' : subgroup G} (f : G →* H) {x : G} (hx : x ∈ G') :
  f x ∈ subgroup.map f G' :=
subgroup.mem_map.mpr ⟨x, hx, rfl⟩

variables {G : Type*} [semi_normed_group G]
variables {H : Type*} [semi_normed_group H]
variables {H₁ : Type*} [normed_group H₁]
variables {K : Type*} [semi_normed_group K]

-- #7474
lemma normed_group.norm_incl {G' : add_subgroup G} (x : G') : ∥incl _ x∥ = ∥x∥ :=
rfl

-- #7474
lemma normed_group_hom.comp_range (f : normed_group_hom G H) (g : normed_group_hom H K) :
(g.comp f).range = add_subgroup.map g.to_add_monoid_hom f.range :=
begin
  erw add_monoid_hom.map_range,
  refl,
end

-- #7474
lemma normed_group_hom.mem_comp_range (f : normed_group_hom G H) (g : normed_group_hom H K) (x : G) :
  g (f x) ∈ (g.comp f).range :=
begin
  rw normed_group_hom.comp_range,
  exact add_subgroup.mem_map_of_mem g.to_add_monoid_hom (mem_range_self x),
end

-- #7474
@[simp]
lemma normed_group.mem_range_incl (G' : add_subgroup G) (x : G) : x ∈ (incl G').range ↔ x ∈ G' :=
begin
  rw normed_group_hom.mem_range,
  split,
  { rintros ⟨y, rfl⟩,
    exact y.property },
  { intro x_in,
    exact ⟨⟨x, x_in⟩, rfl⟩ },
end

-- #7474
@[simp]
lemma normed_group_hom.range_comp_incl_top {f : normed_group_hom G H} :
(f.comp (incl (⊤ : add_subgroup G))).range = f.range :=
begin
  ext x,
  simp only [normed_group_hom.mem_range, incl_apply, normed_group_hom.comp_apply],
  split,
  { rintros ⟨⟨y, h⟩, rfl⟩,
    exact ⟨y, rfl⟩ },
  { rintros ⟨y, rfl⟩,
    exact ⟨⟨y, trivial⟩, rfl⟩ },
end
