import for_mathlib.Profinite.functorial_limit
import locally_constant.NormedGroup

namespace NormedGroup

open opposite locally_constant

variables (X : Profinite) (M : NormedGroup)

lemma locally_constant_factors_fun (f : locally_constant X M) :
  ∃ (I : X.clopen_cover) (g : locally_constant I M), g ∘ I.proj = f :=
begin
  let Us : set (set X) := {U | (∃ m : M, U = f ⁻¹' {m}) ∧ U.nonempty},
  have Us_open : ∀ U ∈ Us, is_open U,
  { rintros U ⟨⟨m, rfl⟩, hU⟩,
    apply f.is_locally_constant },
  have Us_nonempty : ∀ U ∈ Us, (U : set X).nonempty := λ U hU, hU.2,
  have Us_cover : ∀ x : X, ∃ U ∈ Us, x ∈ U,
  { intros x,
    let U := f ⁻¹' { f x },
    refine ⟨U,_, by tauto⟩,
    refine ⟨⟨f x,rfl⟩,⟨x,by tauto⟩⟩ },
  have Us_disjoint : ∀ (U V ∈ Us), (U ∩ V : set X).nonempty → U = V,
  { rintros U V ⟨⟨m,rfl⟩,hU⟩ ⟨⟨n,rfl⟩,hV⟩ h,
    rcases h with ⟨x,h1 : f x = _, h2 : f x = _⟩,
    rw [← h1, h2] },
  let I := Profinite.clopen_cover.of_open_cover Us Us_open Us_nonempty Us_cover Us_disjoint,
  let g_fun : I → M := λ i, f (classical.some (I.nonempty i)),
  have : is_locally_constant g_fun := λ S, is_open_discrete _,
  let g : locally_constant I M := ⟨g_fun, this⟩,
  refine ⟨I,g,_⟩,
  ext x,
  let i : ↥I := ⟨f ⁻¹' { f x }, ⟨⟨f x, rfl⟩, ⟨x, by tauto⟩⟩⟩,
  have : I.proj x = i,
  { symmetry,
    apply Profinite.clopen_cover.proj_fun_unique,
    tauto },
  dsimp,
  rw this,
  have h1 := classical.some_spec (I.nonempty i),
  dsimp at h1,
  simp only [set.mem_preimage, set.mem_singleton_iff] at h1,
  rw ← h1,
  refl,
end

end NormedGroup
