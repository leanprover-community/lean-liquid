import for_mathlib.is_locally_constant
import locally_constant.analysis

/-!
# Extending a locally constant map to larger profinite sets

In this file, we prove that, given a topological embedding `e : X → Y` from a non-empty
compact topological space to a profinite set (ie. compact Hausdorff totally disconnected space),
every locally constant map `f` from `X` to any type `Z` "extends" to a locally constant map
from `Y` to `Z`, ie. there exists `g : Y → Z` locally constant such that `f = g ∘ e`.

     e
  X ↪-→ Y
  |    /
f |   / h
  ↓ ↙
  Z

Notes:
* this wouldn't work if `X` and `Z` were empty and `Y` weren't. The minimal assumption
  would be assuming `Z` isn't empty, I'll refactor this soon.
* Everything is stated assuming only `X` is compact but the existence of `f` ensures `X` is
  profinite, we're just saving type-class search (and nothing in the construction or proofs
  directly use `X` is profinite).

The main definition is `embedding.extend {e : X → Y} (he : embedding e) (f : X → Z) : Y → Z`
It assumes `X` is compact (and non-empty) and assumes `Y` is profinite but doesn't
assume `f` is locally constant, it is simply defined as a constant map if `f` isn't.

The announced properties of this extension are `embedding.extend_extends` and
`embedding.is_locally_constant_extend`.
-/

variables {X : Type*} [topological_space X]

noncomputable theory
open set

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
    apply (V_cl s).diff,
    apply is_clopen_Union,
    intro s',
    by_cases h : s' = s,
    simp [h, is_clopen_empty],
    simp [h, V_cl s'] },
  have R_cl : ∀ s, is_clopen (R s),
  { intro s,
    dsimp [R],
    split_ifs,
    { apply (W_cl s₀).union,
      apply is_clopen.compl,
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

variables {Z : Type*} [inhabited Z]

open_locale classical

def embedding.extend {e : X → Y} (he : embedding e) (f : X → Z) : Y → Z :=
if h : is_locally_constant f ∧ nonempty X then
by { haveI := h.2, exact (h.1.discrete_quotient_map) ∘ (he.discrete_quotient_equiv h.1.discrete_quotient).symm ∘ (he.discrete_quotient_map h.1.discrete_quotient).proj }
else λ y, default Z

/- lemma embedding.extend_eq {e : X → Y} (he : embedding e) {f : X → Z} (hf : is_locally_constant f) :
  he.extend f = (hf.discrete_quotient_map) ∘ (he.discrete_quotient_equiv hf.discrete_quotient).symm ∘ (he.discrete_quotient_map hf.discrete_quotient).proj
  := dif_pos hf -/

lemma embedding.extend_extends {e : X → Y} (he : embedding e) {f : X → Z} (hf : is_locally_constant f) :
∀ x, he.extend f (e x) = f x :=
begin
  intro x,
  haveI : nonempty X := ⟨x⟩,
  let S := hf.discrete_quotient,
  let S' := he.discrete_quotient_map hf.discrete_quotient,
  let barf : S → Z := hf.discrete_quotient_map,
  let g : S ≃ S' := he.discrete_quotient_equiv hf.discrete_quotient,
  unfold embedding.extend,
  have h : is_locally_constant f ∧ nonempty X := ⟨hf, ⟨x⟩⟩,
  rw [dif_pos h],
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

lemma embedding.range_extend {e : X → Y} (he : embedding e)
  [nonempty X] {Z : Type*} [inhabited Z] {f : X → Z} (hf : is_locally_constant f) :
  range (he.extend f) = range f :=
begin
  ext z,
  split,
  { rintro ⟨y, rfl⟩,
    dsimp [embedding.extend],
    rw [dif_pos, ← congr_arg range hf.discrete_quotient_map_proj, range_comp,
      range_iff_surjective.mpr (discrete_quotient.proj_surjective _),
      set.image_univ, function.comp],
    swap, { exact ⟨hf, ‹_›⟩ },
    { exact ⟨_, rfl⟩ } },
  { rintro ⟨x, rfl⟩,
    exact ⟨e x, he.extend_extends hf _⟩ }
end

def embedding.locally_constant_extend {e : X → Y} (he : embedding e) (f : locally_constant X Z) :
  locally_constant Y Z :=
⟨he.extend f, he.is_locally_constant_extend⟩

@[simp]
lemma embedding.locally_constant_extend_extends {e : X → Y} (he : embedding e)
  (f : locally_constant X Z) (x : X) : he.locally_constant_extend f (e x) = f x :=
he.extend_extends f.2 x

lemma embedding.comap_locally_constant_extend {e : X → Y} (he : embedding e)
  (f : locally_constant X Z) : (he.locally_constant_extend f).comap e = f :=
begin
  ext x,
  rw locally_constant.coe_comap _ _ he.continuous,
  exact he.locally_constant_extend_extends f x
end

lemma embedding.range_locally_constant_extend {e : X → Y} (he : embedding e)
  [nonempty X] {Z : Type*} [inhabited Z] (f : locally_constant X Z) :
  range (he.locally_constant_extend f) = range f :=
he.range_extend f.2

-- version avec comap_hom pour Z normed group ?
