import topology.order
import topology.bases
import data.finset.basic

open_locale classical

open topological_space

lemma is_closed_bUnion' {ι X : Type*} [topological_space X]
  (F : finset ι) (Vs : Π (i : ι) (hi : i ∈ F), set X)
  (hVs : ∀ (i : ι) (hi : i ∈ F), is_closed (Vs i hi)) :
  is_closed (⋃ (i : ι) (hi : i ∈ F), Vs i hi) := sorry

lemma topological_basis_pi {ι : Type*} (Xs : ι → Type*)
  [∀ i, topological_space (Xs i)] : is_topological_basis
  { S : set (Π i, Xs i) | ∃ (Us : Π (i : ι), set (Xs i)) (F : finset ι),
    (∀ i, i ∈ F → is_open (Us i)) ∧ S = (F : set ι).pi Us } :=
{ exists_subset_inter := begin
    intros A hA B hB x hx,
    obtain ⟨C,F,hF,rfl⟩ := hA,
    obtain ⟨D,G,hG,rfl⟩ := hB,
    use ((F : set ι).pi C) ∩ ((G : set ι).pi D),
    dsimp,
    let Us : Π (i : ι), set (Xs i) := λ i,
      if i ∈ F ∧ i ∈ G then (C i) ∩ (D i) else
      if i ∈ F then (C i) else
      if i ∈ G then (D i) else set.univ,
    use Us,
    { use F ∪ G,
      split,
      { intros i hi,
        rw finset.mem_union at hi,
        dsimp [Us],
        split_ifs with hh1 hh2 hh3,
        { refine is_open.inter (hF _ hh1.1) (hG _ hh1.2) },
        { exact hF _ hh2 },
        { exact hG _ hh3 },
        { exact is_open_univ } },
      { dsimp [set.pi],
        ext z,
        split,
        { rintro ⟨h1,h2⟩ i hi,
          dsimp [Us],
          split_ifs with hh1 hh2 hh3,
          { refine ⟨h1 _ hh1.1, h2 _ hh1.2⟩ },
          { exact h1 _ hh2 },
          { exact h2 _ hh3 },
          { trivial } },
        { intro h,
          split,
          { intros i hi,
            specialize h i (by finish),
            dsimp [Us] at h,
            split_ifs at h,
            { exact h.1 },
            { exact h } },
          { intros i hi,
            specialize h i (by finish),
            dsimp [Us] at h,
            split_ifs at h,
            { exact h.2 },
            { finish },
            { exact h } } } } },
    { refine ⟨hx, by tauto⟩ }
  end,
  sUnion_eq := begin
    rw set.eq_univ_iff_forall,
    intros x,
    use set.univ,
    use (λ i, set.univ),
    simp [∅],
  end,
  eq_generate_from := by rw pi_eq_generate_from }

variables {X Y : Type*} [topological_space X] [topological_space Y]
  (f : X → Y)

-- TODO: Major golfing required!
lemma pullback_topological_basis (hf : inducing f)  (S : set (set Y))
  (hS : is_topological_basis S) :
  is_topological_basis { A : set X | ∃ (B : set Y) (hB : B ∈ S), A = f ⁻¹' B } :=
{ exists_subset_inter := begin
    rintros T1 ⟨B1,h1,rfl⟩ T2 ⟨B2,h2,rfl⟩ x hx,
    obtain ⟨C,hC,h1,h2⟩ := hS.exists_subset_inter B1 h1 B2 h2 (f x) hx,
    refine ⟨f ⁻¹' C,_,h1,_⟩,
    { dsimp,
      refine ⟨C,hC,rfl⟩ },
    { rw ← set.preimage_inter,
      apply set.preimage_mono,
      exact h2 }
  end,
  sUnion_eq := begin
    have h := hS.sUnion_eq,
    rw set.eq_univ_iff_forall at *,
    intros x,
    specialize h (f x),
    rcases h with ⟨B,hB,hx⟩,
    use f ⁻¹' B,
    use B,
    exact ⟨hB,rfl⟩,
    exact hx,
  end,
  eq_generate_from := begin
    refine le_antisymm _ _,
    { intros U hU,
      change is_open _,
      rw hf.is_open_iff,
      induction hU,
      case topological_space.generate_open.basic : A hA {
        obtain ⟨B,hB,rfl⟩ := hA,
        use B,
        split,
        apply hS.is_open,
        exact hB,
        refl },
      case topological_space.generate_open.univ {
        use set.univ,
        split,
        apply is_open_univ,
        simp },
      case topological_space.generate_open.inter : A B hA hB h1 h2 {
        obtain ⟨U,hU,rfl⟩ := h1,
        obtain ⟨V,hV,rfl⟩ := h2,
        use U ∩ V,
        split,
        apply is_open.inter hU hV,
        simp },
      case topological_space.generate_open.sUnion : Us hUs h {
        dsimp at *,
        let Vs : Us → set Y := λ V, classical.some (h V V.2),
        have hVs := λ (V : Us), classical.some_spec (h V V.2),
        use ⋃ (V : Us), Vs V,
        split,
        { apply is_open_sUnion,
          rintros T ⟨T,rfl⟩,
          dsimp,
          specialize hVs T,
          exact hVs.1 },
        { rw set.preimage_Union,
          ext x,
          split,
          { rintros ⟨A,⟨V,rfl⟩,hx⟩,
            dsimp at hx,
            rw (hVs V).2 at hx,
            use V.1,
            refine ⟨V.2,hx⟩ },
          { rintro ⟨V,hV,hx⟩,
            use V,
            use ⟨V,hV⟩,
            dsimp,
            rw (hVs ⟨V,hV⟩).2,
            refl,
            exact hx } } } },
    { rintros U (hU : is_open _),
      rw hf.is_open_iff at hU,
      rcases hU with ⟨T,hT,rfl⟩,
      replace hT := hS.open_eq_sUnion hT,
      rcases hT with ⟨Ts,hTs,rfl⟩,
      rw set.preimage_sUnion,
      apply generate_open.sUnion,
      rintros B ⟨B,rfl⟩,
      apply generate_open.sUnion,
      rintros C ⟨hB,rfl⟩,
      dsimp,
      apply generate_open.basic,
      use B,
      split,
      apply hTs,
      exact hB,
      refl }
  end }
