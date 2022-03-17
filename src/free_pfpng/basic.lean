import pseudo_normed_group.category
import data.set.intervals
import for_mathlib.Profinite.extend

.

open_locale big_operators

universe u
variable (S : Fintype.{u})

@[derive add_comm_group]
def free_pfpng := S → ℤ

noncomputable theory
open_locale classical

instance : has_nnnorm (free_pfpng S) :=
⟨λ f, ∑ s, ∥f s∥₊⟩

namespace free_pfpng

@[simp] lemma nnnorm_zero : ∥(0 : free_pfpng S)∥₊ = 0 :=
by { change ∑ _, _ = _, simp }

@[simp] lemma nnnorm_neg (f : free_pfpng S) : ∥(-f)∥₊ = ∥f∥₊ :=
by { change ∑ _, _ = _, simpa }

lemma nnnorm_add (f₁ f₂ : free_pfpng S) : ∥f₁ + f₂∥₊ ≤ ∥f₁∥₊ + ∥f₂∥₊ :=
begin
  change ∑ _, _ ≤ ∑ _, _ + ∑ _, _,
  rw ← finset.sum_add_distrib,
  apply finset.sum_le_sum,
  intros s _,
  apply nnnorm_add_le,
end

instance (c) : topological_space { f : free_pfpng S | ∥f∥₊ ≤ c } := ⊥
instance (c) : discrete_topology { f : free_pfpng S | ∥f∥₊ ≤ c } := ⟨rfl⟩

instance (c) : fintype { f : free_pfpng S | ∥f∥₊ ≤ c } :=
begin
  let A := { f : free_pfpng S | ∥f∥₊ ≤ c },
  have h : ∃ (N : ℕ), c ≤ N := sorry, -- ceiling.
  let N := h.some, let hN : c ≤ N := h.some_spec,
  let ι : A → S → set.Icc (-(N : ℤ)) N :=
    λ a s, ⟨a.1 s, _⟩,
  swap, { sorry },
  have : function.injective ι,
  { rintros ⟨f,hf⟩ ⟨g,hg⟩ h,
    ext s,
    apply_fun (λ e, (e s).1) at h,
    assumption },
  apply fintype.of_injective ι this,
end

instance : profinitely_filtered_pseudo_normed_group (free_pfpng S) :=
{ filtration := λ c, { f | ∥ f ∥₊ ≤ c },
  filtration_mono := λ c₁ c₂ h f hf, le_trans hf h,
  zero_mem_filtration := λ c, by simp,
  neg_mem_filtration := λ c f hf, by simpa,
  add_mem_filtration := λ c₁ c₂ f₁ f₂ h₁ h₂,
    le_trans (nnnorm_add _ _ _) (add_le_add h₁ h₂),
  continuous_add' := λ c₁ c₂,
    continuous_of_discrete_topology,
  continuous_neg' := λ c, continuous_of_discrete_topology,
  continuous_cast_le := λ _ _ _, continuous_of_discrete_topology,
  ..(infer_instance : add_comm_group (free_pfpng S)) }

def map {S₁ S₂ : Fintype.{u}} (g : S₁ ⟶ S₂) :
  strict_comphaus_filtered_pseudo_normed_group_hom
  (free_pfpng S₁) (free_pfpng S₂) :=
{ to_fun := λ f s, ∑ t in finset.univ.filter (λ w, g w = s), f t,
  map_zero' := sorry,
  map_add' := sorry,
  strict' := sorry,
  continuous' := λ c, continuous_of_discrete_topology }

@[simp]
lemma map_id : map (𝟙 S) =
  strict_comphaus_filtered_pseudo_normed_group_hom.id :=
sorry

@[simp]
lemma map_comp {S₁ S₂ S₃ : Fintype.{u}}
  (g₁ : S₁ ⟶ S₂) (g₂ : S₂ ⟶ S₃) :
  map (g₁ ≫ g₂) =
  (map g₂).comp (map g₁) :=
sorry

end free_pfpng

@[simps]
def free_pfpng_functor : Fintype ⥤ ProFiltPseuNormGrp₁ :=
{ obj := λ S,
  { M := free_pfpng S,
    exhaustive' := λ f, ⟨∥f∥₊, le_refl _⟩ },
  map := λ S₁ S₂ f, free_pfpng.map f,
  map_id' := free_pfpng.map_id,
  map_comp' := λ _ _ _ g₁ g₂, free_pfpng.map_comp g₁ g₂ }

def free_pfpng_profinite : Profinite.{u} ⥤ ProFiltPseuNormGrp₁ :=
Profinite.extend $ free_pfpng_functor
