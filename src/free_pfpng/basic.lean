import pseudo_normed_group.category
import data.set.intervals
import for_mathlib.Profinite.extend
import condensed.ab

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

lemma norm_eval_le {c : nnreal} {s : S}
  (f : free_pfpng S) (hf : ∥f∥₊ ≤ c) : ∥f s∥₊ ≤ c :=
le_trans (begin
  apply @finset.single_le_sum S nnreal _ (λ t, ∥f t∥₊) finset.univ,
  { intros _ _, apply zero_le },
  { exact finset.mem_univ s }
end) hf

instance (c) : fintype { f : free_pfpng S | ∥f∥₊ ≤ c } :=
begin
  let A := { f : free_pfpng S | ∥f∥₊ ≤ c },
  have h : ∃ (N : ℕ), c ≤ N := ⟨nat.ceil c, nat.le_ceil c⟩,
  let N := h.some, let hN : c ≤ N := h.some_spec,
  let ι : A → S → set.Icc (-(N : ℤ)) N :=
    λ a s, ⟨a.1 s, _, _⟩,
  rotate,
  { -- I'm sure there is a more efficient way to do this...
    have : - ∥a.val s∥ ≤ a.val s := neg_abs_le_self ↑(a.val s),
    replace this : - (c : ℝ) ≤ a.val s := le_trans _ this,
    swap,
    { simp only [subtype.val_eq_coe, neg_le_neg_iff],
      exact_mod_cast (norm_eval_le S a.val a.2) },
    replace this : -(N : ℝ) ≤ _ := le_trans _ this,
    swap,
    { rw [neg_le_neg_iff], exact_mod_cast hN },
    exact_mod_cast this },
  { have : ↑(a.val s) ≤ ∥a.val s∥ := le_max_left _ _,
    replace this : ↑(a.val s) ≤ (c : ℝ) := le_trans this _,
    swap, { exact_mod_cast (norm_eval_le S a.val a.2) },
    replace this := le_trans this hN,
    push_cast at this,
    exact_mod_cast this },
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
  map_zero' := by simpa,
  map_add' := λ f g, by simpa [finset.sum_add_distrib],
  strict' := begin
    intros c f hf,
    refine le_trans _ hf,
    change ∑ s₂, ∥(∑ t in finset.univ.filter (λ w, g w = s₂), f t)∥₊ ≤
      ∑ s₁, _,
    have : ∑ s₂, ∥(∑ t in finset.univ.filter (λ w, g w = s₂), f t)∥₊ ≤
      ∑ s₂ : S₂, ∑ t in finset.univ.filter (λ w, g w = s₂), ∥f t∥₊,
    { apply finset.sum_le_sum,
      intros i _,
      apply nnnorm_sum_le },
    refine le_trans this _,
    rw ← finset.sum_bUnion,
    apply le_of_eq,
    apply finset.sum_congr,
    { rw finset.eq_univ_iff_forall,
      intros x,
      rw finset.mem_bUnion,
      use [g x, by simp] },
    { intros s₁ _, refl },
    { intros x _ y _ h,
      rintros a hh,
      apply h,
      simp only [finset.inf_eq_inter, finset.mem_inter, finset.mem_filter,
        finset.mem_univ, true_and] at hh,
      rw [← hh.1, ← hh.2] }
  end,
  continuous' := λ c, continuous_of_discrete_topology }

@[simp]
lemma map_id : map (𝟙 S) =
  strict_comphaus_filtered_pseudo_normed_group_hom.id :=
begin
  ext s,
  dsimp [map],
  simp [finset.filter_congr_decidable, finset.sum_filter],
end

@[simp]
lemma map_comp {S₁ S₂ S₃ : Fintype.{u}}
  (g₁ : S₁ ⟶ S₂) (g₂ : S₂ ⟶ S₃) :
  map (g₁ ≫ g₂) =
  (map g₂).comp (map g₁) :=
begin
  ext s₃,
  dsimp [map],
  erw ← finset.sum_bUnion,
  apply finset.sum_congr,
  { ext s,
    split,
    { intro h, simp only [finset.mem_filter, finset.mem_univ, true_and] at h,
      rw finset.mem_bUnion,
      use [g₁ s, by simpa] },
    { intro h, simp only [finset.mem_bUnion, finset.mem_filter,
      finset.mem_univ, true_and, exists_prop, exists_eq_right'] at h,
      simpa, } },
  { intros s₁ h,
    rw finset.mem_bUnion at h },
  { intros x hx y hy,
    simp only [finset.coe_filter, finset.coe_univ, set.sep_univ,
      set.mem_set_of_eq] at hx hy,
    intros h a ha,
    simp only [finset.inf_eq_inter, finset.mem_inter, finset.mem_filter,
      finset.mem_univ, true_and] at ha,
    apply h, rw [← ha.1, ← ha.2] }
end

end free_pfpng

@[simps]
def free_pfpng_functor : Fintype ⥤ ProFiltPseuNormGrp₁ :=
{ obj := λ S,
  { M := free_pfpng S,
    exhaustive' := λ f, ⟨∥f∥₊, le_refl _⟩ },
  map := λ S₁ S₂ f, free_pfpng.map f,
  map_id' := free_pfpng.map_id,
  map_comp' := λ _ _ _ g₁ g₂, free_pfpng.map_comp g₁ g₂ }

def Fintype.free_pfpng (T : Fintype) : ProFiltPseuNormGrp₁ :=
free_pfpng_functor.obj T

def Fintype.free_pfpng_unit :
  Fintype.to_Profinite ⟶ free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.level.obj 1 :=
{ app := λ S,
  { to_fun := λ s,
    { val := λ t, if t = s then 1 else 0,
      property := sorry },
    continuous_to_fun := continuous_bot },
  naturality' := sorry }

def Profinite.free_pfpng (S : Profinite) : ProFiltPseuNormGrp₁ :=
(Profinite.extend free_pfpng_functor).obj S

open category_theory
open category_theory.limits

def Profinite.free_pfpng_level_iso (S : Profinite.{u}) (r) :
  (ProFiltPseuNormGrp₁.level.obj r).obj S.free_pfpng ≅
  limits.limit (S.fintype_diagram ⋙ free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.level.obj r) :=
(is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj r)
  (limit.is_limit _)).cone_point_unique_up_to_iso $ limit.is_limit _

def Profinite.to_free_pfpng (S : Profinite.{u}) :
  S ⟶ (ProFiltPseuNormGrp₁.level.obj 1).obj S.free_pfpng :=
(limit.is_limit _).map S.as_limit_cone (whisker_left _ $ Fintype.free_pfpng_unit) ≫
(S.free_pfpng_level_iso 1).inv

--(limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj 1) (limits.limit.is_limit _)).map
--  S.as_limit_cone $ whisker_left _ (Fintype.free_pfpng_unit) ≫ (functor.associator _ _ _).inv

def Profinite.free_pfpng_π (S : Profinite) (T : discrete_quotient S) :
  S.free_pfpng ⟶ (Fintype.of T).free_pfpng :=
category_theory.limits.limit.π _ _
