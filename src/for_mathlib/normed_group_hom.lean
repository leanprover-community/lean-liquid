import analysis.normed_space.normed_group_hom
import topology.algebra.normed_group

import for_mathlib.normed_group

noncomputable theory

open set normed_group_hom uniform_space


-- PR to group_theory.subgroup, next to subgroup.mem_map
@[to_additive]
lemma subgroup.mem_map_of_mem {G H : Type*} [group G] [group H] {G' : subgroup G} (f : G →* H) {x : G} (hx : x ∈ G') :
  f x ∈ subgroup.map f G' :=
subgroup.mem_map.mpr ⟨x, hx, rfl⟩

variables {G : Type*} [normed_group G]
variables {H : Type*} [normed_group H]
variables {K : Type*} [normed_group K]

lemma normed_group.norm_incl {G' : add_subgroup G} (x : G') : ∥incl _ x∥ = ∥x∥ :=
rfl

lemma normed_group_hom.comp_range (f : normed_group_hom G H) (g : normed_group_hom H K) :
(g.comp f).range = add_subgroup.map g.to_add_monoid_hom f.range :=
begin
  erw add_monoid_hom.map_range,
  refl,
end

lemma normed_group_hom.mem_comp_range (f : normed_group_hom G H) (g : normed_group_hom H K) (x : G) :
  g (f x) ∈ (g.comp f).range :=
begin
  rw normed_group_hom.comp_range,
  exact add_subgroup.mem_map_of_mem g.to_add_monoid_hom (mem_range_self x),
end

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

@[simp]
lemma normed_group_hom.ker_zero : (0 : normed_group_hom G H).ker = ⊤ :=
by { ext, simp [normed_group_hom.mem_ker] }

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

lemma normed_group_hom.ker_eq_preimage (f : normed_group_hom G H) :
  (f.ker : set G) = (f : G → H) ⁻¹' {0} :=
by { ext, erw f.mem_ker }

lemma normed_group_hom.is_closed_ker (f : normed_group_hom G H) : is_closed (f.ker : set G) :=
f.ker_eq_preimage ▸ is_closed.preimage f.continuous (t1_space.t1 0)
