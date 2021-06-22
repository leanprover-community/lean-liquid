import data.fintype.basic

open_locale classical

lemma exists_le_finset {α : Type*} [inhabited α] [semilattice_inf α]
  (G : finset α) : ∃ j : α, ∀ g ∈ G, j ≤ g :=
begin
  apply G.induction_on,
  refine ⟨(default α), by tauto⟩,
  rintros a S ha ⟨j0,h0⟩,
  use a ⊓ j0,
  intros g hg,
  rw finset.mem_insert at hg,
  cases hg,
  { rw hg,
    exact inf_le_left },
  { exact le_trans inf_le_right (h0 _ hg) },
end

lemma Inter_eq {α β : Type*} [inhabited α] [fintype β] [semilattice_inf α]
  (i : α) (f : Π (a : α) (ha : a ≤ i), set β)
  (hf : ∀ (a b : α) (ha : a ≤ i) (hb : b ≤ i) (h : a ≤ b), f a ha ≤ f b hb) :
  (∃ (j : α) (hj : j ≤ i), (⋂ (k : α) (hk : k ≤ i), f k hk) = f j hj) :=
begin
  suffices :
    (∃ (j : α) (hj : j ≤ i), ∀ (k : α) (hk : k ≤ i), f j hj ≤ f k hk),
  { rcases this with ⟨j,hj,h⟩,
    use j,
    use hj,
    refine le_antisymm _ _,
    { refine set.sInter_subset_of_mem ⟨j, _⟩,
      tidy },
    { rintros x hx _ ⟨k,rfl⟩,
      rintro _ ⟨hk,rfl⟩,
      apply h _ _ hx } },
  let BB := {S : set β | ∃ (e : α) (he : e ≤ i), S = f e he },
  let FF : BB → α := λ ee, classical.some ee.2,
  have hFF : ∀ S : BB, FF S ≤ i := λ S, (classical.some_spec S.2).some,
  have hFF' : ∀ S : BB, (S : set β) = f (FF S) (hFF S) := λ S, (classical.some_spec S.2).some_spec,
  haveI : fintype BB := fintype.of_injective (λ S : BB, S.1) (by tidy),
  let GG := (finset.univ : finset BB).image FF,
  obtain ⟨j0,hj0⟩ := exists_le_finset GG,
  use [j0 ⊓ i, inf_le_right],
  intros k hk,
  have : ∃ (e : α) (he : e ≤ i) (heFF : e ∈ GG), f k hk = f e he,
  { let T : BB := ⟨f k hk, k, hk, rfl⟩,
    use [FF T, hFF _],
    split,
    { erw finset.mem_image,
      use T,
      simp },
    { rw ← hFF', refl, } },
  obtain ⟨e,he,heFF,hhe⟩ := this,
  rw hhe,
  exact hf _ _ _ _ (le_trans inf_le_left (hj0 _ heFF)),
end

lemma eventually_constant {α β : Type*} [inhabited α] [fintype β] [semilattice_inf α]
  (i : α) (f : Π (a : α) (ha : a ≤ i), set β)
  (hf : ∀ (a b : α) (ha : a ≤ i) (hb : b ≤ i) (h : a ≤ b), f a ha ≤ f b hb) :
  (∃ (j : α) (hj : j ≤ i), ∀ (k : α) (hk : k ≤ j), f k (le_trans hk hj) = f j hj) :=
begin
  let S := ⋂ (k : α) (hk : k ≤ i), f k hk,
  obtain ⟨j0,hj0,h⟩ := Inter_eq i f hf,
  use [j0, hj0],
  intros e he,
  refine le_antisymm (hf _ _ _ _ he) _,
  rw ← h,
  rintros x hx,
  refine hx _ ⟨e, _⟩,
  tidy
end
