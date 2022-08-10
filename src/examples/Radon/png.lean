import examples.Radon.main
import category_theory.limits.concrete_category

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space


namespace Profinite

variables (X : Profinite.{0}) (p : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)]

instance why_do_I_need_this : add_comm_group (weak_dual ℝ C(X,ℝ)) :=
show add_comm_group (C(X,ℝ) →L[ℝ] ℝ), by apply_instance

lemma bdd_add {ca cb} (a b : weak_dual ℝ C(X,ℝ)) (ha : a.bdd p ca) (hb : b.bdd p cb) :
  (a + b).bdd p (ca + cb) := sorry

lemma bdd_zero : (0 : weak_dual ℝ C(X,ℝ)).bdd p 0 := sorry

lemma bdd_neg {c} (a : weak_dual ℝ C(X,ℝ)) (ha : a.bdd p c) : (-a).bdd p c := sorry

def bdd_weak_dual : add_subgroup (weak_dual ℝ C(X,ℝ)) :=
{ carrier := { μ | ∃ c, μ.bdd p c },
  add_mem' := λ a b ha hb, begin
    obtain ⟨ca, ha⟩ := ha,
    obtain ⟨cb, hb⟩ := hb,
    use ca + cb,
    apply bdd_add _ _ _ _ ha hb,
  end,
  zero_mem' := ⟨0, bdd_zero _ _⟩,
  neg_mem' := λ a ha, begin
    obtain ⟨c,ha⟩ := ha,
    use c,
    apply bdd_neg _ _ _ ha,
  end }

instance : pseudo_normed_group (X.bdd_weak_dual p) :=
{ filtration := λ c, {μ | μ.1.bdd p c},
  filtration_mono := λ c₁ c₂ h μ hμ e, by apply le_trans (hμ e) h,
  zero_mem_filtration := λ c e, le_trans (bdd_zero _ _ _) (zero_le _),
  neg_mem_filtration := λ c μ hμ e, bdd_neg _ _ _ hμ _,
  add_mem_filtration := λ c₁ c₂ a b ha hb, bdd_add _ _ _ _ ha hb }

instance topological_space_bdd_weak_dual_filtration (c : ℝ≥0) :
  topological_space (pseudo_normed_group.filtration (X.bdd_weak_dual p) c) :=
topological_space.induced (λ μ, μ.1.1) infer_instance

def bdd_weak_dual_filtration_homeo (c : ℝ≥0) :
  (pseudo_normed_group.filtration (X.bdd_weak_dual p) c) ≃ₜ
  X.Radon p c :=
{ to_fun := λ μ, ⟨μ.1.1, μ.2⟩,
  inv_fun := λ μ, ⟨⟨μ.1, ⟨c, μ.2⟩⟩, μ.2⟩,
  left_inv := λ μ, by { ext, refl },
  right_inv := λ μ, by { ext, refl },
  continuous_to_fun := sorry,
  continuous_inv_fun := sorry }

instance : comphaus_filtered_pseudo_normed_group (X.bdd_weak_dual p) :=
{ t2 := λ c, (X.bdd_weak_dual_filtration_homeo p c).symm.t2_space,
  compact := λ c, (X.bdd_weak_dual_filtration_homeo p c).symm.compact_space,
  continuous_add' := sorry,
  continuous_neg' := sorry,
  continuous_cast_le := sorry,
  ..(infer_instance : pseudo_normed_group (X.bdd_weak_dual p)) }

def Radon_png : CompHausFiltPseuNormGrp₁ :=
{ M := X.bdd_weak_dual p,
  exhaustive' := λ μ, μ.2 }

def map_Radon_png {X Y : Profinite.{0}} (f : X ⟶ Y) :
  X.Radon_png p ⟶ Y.Radon_png p :=
{ to_fun := λ μ, ⟨weak_dual.comap f.comap μ.1, begin
    obtain ⟨c,hc⟩ := μ.2,
    use c,
    apply weak_dual.bdd_comap _ hc,
    apply_instance,
  end⟩,
  map_zero' := by { ext, refl },
  map_add' := λ a b, by { ext, refl },
  strict' := λ c μ hμ,
    weak_dual.bdd_comap _ hμ _,
  continuous' := sorry }

def Radon_png_functor : Profinite.{0} ⥤ CompHausFiltPseuNormGrp₁ :=
{ obj := λ X, X.Radon_png p,
  map := λ X Y, map_Radon_png _,
  map_id' := λ X, by { ext, dsimp [map_Radon_png, weak_dual.comap], congr' 1,
    ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

def Radon_png_cone : cone (X.diagram ⋙ Radon_png_functor p) :=
(Radon_png_functor p).map_cone X.as_limit_cone

def Radon_png_functor_level_iso_component (c : ℝ≥0) (X : Profinite.{0}) :
  (CompHausFiltPseuNormGrp₁.level.obj c).obj (X.Radon_png p) ≅
  (Radon_CompHaus_functor p c).obj X :=
let e := (bdd_weak_dual_filtration_homeo X p c) in
{ hom := e.to_continuous_map,
  inv := e.symm.to_continuous_map,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def Radon_png_functor_level_iso (c : ℝ≥0) :
  Radon_png_functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ≅
  Radon_CompHaus_functor p c :=
nat_iso.of_components
(λ X, Radon_png_functor_level_iso_component _ _ _)
(λ X Y f, by { ext, refl })

def is_limit_Radon_png_cone_map_level (c : ℝ≥0) :
  is_limit ((Radon_png_functor p ⋙
    CompHausFiltPseuNormGrp₁.level.obj c).map_cone X.as_limit_cone) :=
{ lift := λ S,
    (X.is_limit_Radon_CompHaus_cone p c).lift
    ⟨_, S.π ≫ whisker_left _ (Radon_png_functor_level_iso p c).hom⟩ ≫
    (Radon_png_functor_level_iso p c).inv.app _,
  fac' := sorry,
  uniq' := sorry }

def is_limit_Radon_png_cone : is_limit (X.Radon_png_cone p) :=
sorry

end Profinite
