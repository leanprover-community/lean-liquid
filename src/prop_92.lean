import topology.separation
import topology.locally_constant.basic
import topology.discrete_quotient
import data.setoid.partition

import for_mathlib.data_setoid_partition
import for_mathlib.topology

import pseudo_normed_group.CLC

noncomputable theory

open_locale nnreal

variables {X : Type*} [topological_space X]

open set

section

lemma is_locally_constant.is_closed_fiber {X Y : Type*} [topological_space X] [topological_space Y]
  [t1_space Y] {f : X → Y} (h : is_locally_constant f) (y : Y) : is_closed (f ⁻¹' {y}) :=
is_closed_singleton.preimage h.continuous

lemma is_locally_constant.is_clopen_fiber {X Y : Type*} [topological_space X] [topological_space Y]
  [t1_space Y] {f : X → Y} (h : is_locally_constant f) (y : Y) : is_clopen (f ⁻¹' {y}) :=
⟨h.is_open_fiber y, h.is_closed_fiber y⟩

end

section
variables {Y : Type*} [topological_space Y]  [t1_space Y]

/-- The discrete quotient of `X` associated to a locally constant `f : X → Y` is associated
to the relation `x ∼ x'` if `f x' = f x`. The weird ordering guarantees that
`{x' | x ∼ x'} = f ⁻¹' {x}`.
-/
def is_locally_constant.discrete_quotient {f : X → Y} (hf : is_locally_constant f) :
  discrete_quotient X :=
{ rel := λ x x', f x' = f x,
  equiv := ⟨λ _, rfl, λ x x', eq.symm, λ x₁ x₂ x₃ h h', by rwa h'⟩,
  clopen := λ x, hf.is_clopen_fiber (f x) }

/-- The map induced by a locally constant map `f : X → Y` from the associated discrete quotient
to `Y`. -/
def is_locally_constant.discrete_quotient_map {f : X → Y} (hf : is_locally_constant f) :
  hf.discrete_quotient → Y :=
@quotient.lift _ _ hf.discrete_quotient.setoid f (λ x x', eq.symm)

@[simp]
lemma is_locally_constant.discrete_quotient_map_proj_apply {f : X → Y} (hf : is_locally_constant f) (x : X) :
hf.discrete_quotient_map (hf.discrete_quotient.proj x) = f x := rfl

@[simp]
lemma is_locally_constant.discrete_quotient_map_proj {f : X → Y} (hf : is_locally_constant f) :
hf.discrete_quotient_map ∘ hf.discrete_quotient.proj = f := funext (λ x, rfl)


def indexed_partition.discrete_quotient {ι : Type*} {s : ι → set X} (h_part : indexed_partition s)
  (h_cl : ∀ i, is_clopen $ s i) : discrete_quotient X :=
{ rel := h_part.setoid.rel,
  equiv := h_part.setoid.iseqv,
  clopen := begin
    intro x,
    rw h_part.class_of,
    apply h_cl
  end }

variables {ι : Type*} {s : ι → set X} (h_cl : ∀ i, is_clopen $ s i)
(h_part : indexed_partition s)

def indexed_partition.discrete_quotient_equiv : ι ≃ h_part.discrete_quotient h_cl :=
h_part.equiv_quotient


lemma indexed_partition.discrete_quotient_fiber (x : h_part.discrete_quotient h_cl) :
  (h_part.discrete_quotient h_cl).proj ⁻¹' {x} = s ((h_part.discrete_quotient_equiv h_cl).symm x) :=
h_part.proj_fiber _

end

section

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

lemma embedding.ex_discrete_quotient [nonempty X] {f : X → Y} (hf : embedding f) (S : discrete_quotient X) :
  ∃ (S' : discrete_quotient Y) (g : S ≃ S'), S'.proj ∘ f = g ∘ S.proj :=
begin
  classical,
  inhabit X,
  haveI : fintype S := discrete_quotient.fintype S,
  have : ∀ s : S, ∃ V : set Y, is_clopen V ∧ S.proj ⁻¹' {s} = f ⁻¹' V,
    from λ s, hf.preimage_clopen (S.fiber_clopen {s}),
  choose V hV using this,
  rw forall_and_distrib at hV,
  cases hV with V_cl hV,
  let s₀ := S.proj (default X),
  let W : S → set Y := λ s, (V s) \ (⋃ s' (h : s' ≠ s), V s'),
  have W_dis : ∀ {s s'}, s ≠ s' → disjoint (W s) (W s'),
  { rintros s s' hss x ⟨⟨hxs_in, hxs_out⟩, ⟨hxs'_in, hxs'_out⟩⟩,
    apply hxs'_out,
    rw mem_bUnion_iff',
    exact ⟨s, hss, hxs_in⟩ },
  have hfW : ∀ x, f x ∈ W (S.proj x),
  { intro x,
    split,
    { change x ∈ f ⁻¹' (V $ S.proj x),
      rw ← hV (S.proj x),
      exact mem_singleton _ },
    { intro h,
      rcases mem_bUnion_iff'.mp h with ⟨s', hss', hfx : x ∈ f ⁻¹' (V s')⟩,
      rw ← hV s' at hfx,
      exact hss' hfx.symm } },
  have W_nonempty : ∀ s, (W s).nonempty,
  { intro s,
    obtain ⟨x, hx : S.proj x = s⟩ := S.proj_surjective s,
    use f x,
    rw ← hx,
    apply hfW,
     },
  let R : S → set Y := λ s, if s = s₀ then W s₀ ∪ (⋃ s, W s)ᶜ else W s,
  have W_cl : ∀ s, is_clopen (W s),
  { intro s,
    apply is_clopen_diff (V_cl s),
    apply is_clopen_Union,
    intro s',
    by_cases h : s' = s,
    simp [h, is_clopen_empty],
    simp [h, V_cl s'] },
  have R_cl : ∀ s, is_clopen (R s),
  { intro s,
    dsimp [R],
    split_ifs,
    { apply is_clopen_union (W_cl s₀),
      apply is_clopen_compl,
      exact is_clopen_Union W_cl },
    { exact W_cl _ }, },
  let R_part : indexed_partition R,
  { apply indexed_partition.mk',
    { rintros s s' hss x ⟨hxs, hxs'⟩,
      dsimp [R] at hxs hxs',
      split_ifs at hxs hxs' with hs hs',
      { exact (hss (hs.symm ▸ hs' : s = s')).elim },
      { cases hxs' with hx hx,
        { exact W_dis hs' ⟨hxs, hx⟩ },
        { apply hx,
          rw mem_Union,
          exact ⟨s, hxs⟩ } },
      { cases hxs with hx hx,
        { exact W_dis hs ⟨hxs', hx⟩ },
        { apply hx,
          rw mem_Union,
          exact ⟨s', hxs'⟩ } },
      { exact W_dis hss ⟨hxs, hxs'⟩ } },
    { intro s,
      dsimp [R],
      split_ifs,
      { use (W_nonempty s₀).some,
        left,
        exact (W_nonempty s₀).some_mem },
      { apply W_nonempty } },
    { intro y,
      by_cases hy : ∃ s, y ∈ W s,
      { cases hy with s hys,
        use s,
        dsimp [R],
        split_ifs,
        { left,
          rwa h at hys },
        { exact hys } },
      { use s₀,
        simp only [R, if_pos rfl],
        right,
        rwa [mem_compl_iff, mem_Union] } } },
  let S' := R_part.discrete_quotient R_cl,
  let g := R_part.discrete_quotient_equiv R_cl,
  have hR : ∀ x, f x ∈ R (S.proj x),
  { intros x,
    by_cases hx : S.proj x = s₀,
    { simp only [hx, R, if_pos rfl],
      left,
      rw ← hx,
      apply hfW },
    { simp only [R, if_neg hx],
      apply hfW }, },
  use [S', g],
  ext x,
  change f x ∈ S'.proj ⁻¹' {g (S.proj x)},
  rw R_part.discrete_quotient_fiber R_cl,
  simpa using hR x,
end

def embedding.discrete_quotient_map [nonempty X] {f : X → Y} (hf : embedding f) (S : discrete_quotient X) :
discrete_quotient Y := (hf.ex_discrete_quotient S).some

def embedding.discrete_quotient_equiv [nonempty X] {f : X → Y} (hf : embedding f) (S : discrete_quotient X) :
  S ≃ hf.discrete_quotient_map S :=
(hf.ex_discrete_quotient S).some_spec.some

lemma embedding.discrete_quotient_spec [nonempty X] {f : X → Y} (hf : embedding f) (S : discrete_quotient X) :
(hf.discrete_quotient_map S).proj ∘ f = (hf.discrete_quotient_equiv S) ∘ S.proj :=
(hf.ex_discrete_quotient S).some_spec.some_spec

variables {Z : Type*} [topological_space Z]  [t1_space Z] [nonempty X]

open_locale classical

def embedding.extend
  {e : X → Y} (he : embedding e) (f : X → Z)
   : Y → Z :=
if hf : is_locally_constant f then
(hf.discrete_quotient_map) ∘ (he.discrete_quotient_equiv hf.discrete_quotient).symm ∘ (he.discrete_quotient_map hf.discrete_quotient).proj
else λ y, f (classical.arbitrary X)

lemma embedding.extend_eq {e : X → Y} (he : embedding e) {f : X → Z} (hf : is_locally_constant f) :
  he.extend f = (hf.discrete_quotient_map) ∘ (he.discrete_quotient_equiv hf.discrete_quotient).symm ∘ (he.discrete_quotient_map hf.discrete_quotient).proj
  := dif_pos hf


lemma embedding.extend_extends {e : X → Y} (he : embedding e) {f : X → Z} (hf : is_locally_constant f) :
∀ x, he.extend f (e x) = f x :=
begin
  intro x,
  let S := hf.discrete_quotient,
  let S' := he.discrete_quotient_map hf.discrete_quotient,
  let barf : S → Z := hf.discrete_quotient_map,
  let g : S ≃ S' := he.discrete_quotient_equiv hf.discrete_quotient,
  rw he.extend_eq hf,
  change (barf ∘ g.symm ∘ (S'.proj ∘ e)) x = f x,
  suffices : (barf ∘ S.proj) x = f x, by simpa [he.discrete_quotient_spec],
  simp
end

lemma embedding.is_locally_constant_extend {e : X → Y} (he : embedding e) {f : X → Z} :
  is_locally_constant (he.extend f) :=
begin
  unfold embedding.extend,
  split_ifs,
  { apply is_locally_constant.comp,
    apply is_locally_constant.comp,
    exact discrete_quotient.proj_is_locally_constant _ },
  { apply is_locally_constant.const },
end

end

namespace CLCFP

variables {r r' : ℝ≥0} (V : NormedGroup) [normed_with_aut r V] (c c₁ c₂ : ℝ≥0) (n : ℕ)
variables [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)]
variables (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ)

include r

def Tinv_sub_T_inv :=
(CLCFP.Tinv V r' c₁ c₂ n).app M - (CLCFP.res V r' c₁ c₂ n ≫ CLCFP.T_inv r V r' c₂ n).app M

lemma Tinv_sub_T_inv_bound_by : (Tinv_sub_T_inv V c₁ c₂ n M).bound_by (r⁻¹ + 1) :=
begin
  rw [Tinv_sub_T_inv, sub_eq_neg_add],
  refine normed_group_hom.bound_by.add _ _,
  { refine (normed_group_hom.bound_by.comp' 1 r⁻¹ r⁻¹ (mul_one _).symm _ _).neg,
    { exact CLC.T_inv_bound_by r V _ },
    { exact (res_norm_noninc V r' c₁ c₂ n M).bound_by_one } },
  { refine NormedGroup.Completion_map_bound_by _ _ _,
    exact (NormedGroup.LocallyConstant_obj_map_norm_noninc _ _ _ _).bound_by_one },
end

variables {V c n M}

/-- 9.2 of Analytic.pdf -/
lemma Tinv_sub_T_inv_exists_preimage (f : (CLCFP V r' (r' * c) n).obj M) (ε : ℝ) (hε : 0 < ε) :
  ∃ g : (CLCFP V r' c n).obj M, Tinv_sub_T_inv V c (r' * c) n M g = f ∧
    (∥g∥ ≤ r / (1 - r) * (1 + ε) * ∥f∥) :=
begin
  sorry
end

variables (V c n M)

lemma Tinv_sub_T_inv_surjective : function.surjective (Tinv_sub_T_inv V c (r' * c) n M) :=
begin
  intros f,
  obtain ⟨g, hg, -⟩ := Tinv_sub_T_inv_exists_preimage f 1 zero_lt_one,
  exact ⟨g, hg⟩
end

end CLCFP
