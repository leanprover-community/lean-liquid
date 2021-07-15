import pseudo_normed_group.CLC
/-!

# V-hat((M_c)^n)^{T⁻¹}

This file defines a fundamental construction defined just above Definition 9.3
in `analytic.pdf`: the subspac of V-hat(M_c^n) where the two actions of T⁻¹ coincide.

## Main definition

Here `M` is a profinitely filtered pseudo-normed group with `T⁻¹` scaling things by `r'`,
`V` is a seminormed group with `T⁻¹` scaling norms by `r`, `c` is a real (a filtration coefficient)
and `n` is a natural.

- `CLCFPTinv r V r' c n M`: the seminormed group defined as the subgroup of `V-hat(M_c^n)` where
  the two actions of `T⁻¹` (one coming from the action on M, the other coming from the
  action on V) coincide.

-/
open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow

namespace category_theory

theorem comm_sq₂ {C} [category C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}
  {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂} {f₃ : A₃ ⟶ B₃}
  {a : A₁ ⟶ A₂} {a' : A₂ ⟶ A₃} {b : B₁ ⟶ B₂} {b' : B₂ ⟶ B₃}
  (h₁ : a ≫ f₂ = f₁ ≫ b) (h₂ : a' ≫ f₃ = f₂ ≫ b') : (a ≫ a') ≫ f₃ = f₁ ≫ b ≫ b' :=
by rw [category.assoc, h₂, ← category.assoc, h₁, ← category.assoc]

end category_theory

open SemiNormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group category_theory.limits
open normed_group_hom

namespace SemiNormedGroup

def equalizer {V W : SemiNormedGroup} (f g : V ⟶ W) := of (f.equalizer g)

namespace equalizer

def ι {V W : SemiNormedGroup} (f g : V ⟶ W) :
  equalizer f g ⟶ V :=
normed_group_hom.equalizer.ι _ _

@[reassoc] lemma condition {V W : SemiNormedGroup} (f g : V ⟶ W) :
  ι f g ≫ f = ι f g ≫ g :=
normed_group_hom.equalizer.condition _ _

lemma ι_range {V W : SemiNormedGroup} (f g : V ⟶ W) :
  (ι f g).range = (f - g).ker :=
begin
  ext, rw [normed_group_hom.mem_range, normed_group_hom.mem_ker],
  split,
  { rintro ⟨x, rfl⟩, rw [normed_group_hom.sub_apply], exact x.2 },
  { intro h, refine ⟨⟨x, h⟩, rfl⟩, }
end

lemma ι_range' {V W : SemiNormedGroup} (f g : V ⟶ W) :
  (ι f g).range = (g - f).ker :=
begin
  rw ι_range, ext x,
  simp only [normed_group_hom.mem_ker, normed_group_hom.sub_apply, sub_eq_zero],
  rw eq_comm
end

def map {V₁ V₂ W₁ W₂ : SemiNormedGroup} {f₁ f₂ g₁ g₂} (φ : V₁ ⟶ V₂) (ψ : W₁ ⟶ W₂)
  (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ) :
  equalizer f₁ g₁ ⟶ equalizer f₂ g₂ :=
normed_group_hom.equalizer.map _ _ hf.symm hg.symm

theorem map_congr
  {V₁ V₂ W₁ W₂ : SemiNormedGroup} {f₁ f₂ g₁ g₂} {φ : V₁ ⟶ V₂} {ψ : W₁ ⟶ W₂}
  {V₁' V₂' W₁' W₂' : SemiNormedGroup} {f₁' f₂' g₁' g₂'} {φ' : V₁' ⟶ V₂'} {ψ' : W₁' ⟶ W₂'}
  {hf : φ ≫ f₂ = f₁ ≫ ψ} {hg : φ ≫ g₂ = g₁ ≫ ψ}
  {hf' : φ' ≫ f₂' = f₁' ≫ ψ'} {hg' : φ' ≫ g₂' = g₁' ≫ ψ'}
  (Hφ : arrow.mk φ = arrow.mk φ') (Hψ : arrow.mk ψ = arrow.mk ψ')
  (Hf₁ : arrow.mk f₁ = arrow.mk f₁') (Hf₂ : arrow.mk f₂ = arrow.mk f₂')
  (Hg₁ : arrow.mk g₁ = arrow.mk g₁') (Hg₂ : arrow.mk g₂ = arrow.mk g₂') :
  arrow.mk (map φ ψ hf hg) = arrow.mk (map φ' ψ' hf' hg') :=
by { cases Hφ, cases Hψ, cases Hf₁, cases Hf₂, cases Hg₁, cases Hg₂, refl }

lemma map_comp_map {V₁ V₂ V₃ W₁ W₂ W₃ : SemiNormedGroup} {f₁ f₂ f₃ g₁ g₂ g₃}
  {φ : V₁ ⟶ V₂} {ψ : W₁ ⟶ W₂} {φ' : V₂ ⟶ V₃} {ψ' : W₂ ⟶ W₃}
  (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ)
  (hf' : φ' ≫ f₃ = f₂ ≫ ψ') (hg' : φ' ≫ g₃ = g₂ ≫ ψ') :
  map φ ψ hf hg ≫ map φ' ψ' hf' hg' =
  map (φ ≫ φ') (ψ ≫ ψ') (comm_sq₂ hf hf') (comm_sq₂ hg hg') :=
by { ext, refl }

lemma map_id {J} [category J] {V W : SemiNormedGroup} (f g : V ⟶ W) :
  map (𝟙 V) (𝟙 W) (show 𝟙 V ≫ f = f ≫ 𝟙 W, by simp) (show 𝟙 V ≫ g = g ≫ 𝟙 W, by simp) = 𝟙 _ :=
by { ext, refl }

lemma norm_map_le {V₁ V₂ W₁ W₂ : SemiNormedGroup} {f₁ f₂ g₁ g₂} {φ : V₁ ⟶ V₂} {ψ : W₁ ⟶ W₂}
  (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ) (C : ℝ) (hφ : ∥ι f₁ g₁ ≫ φ∥ ≤ C) :
  ∥map φ ψ hf hg∥ ≤ C :=
normed_group_hom.equalizer.norm_map_le _ _ C hφ

@[simps obj map]
protected def F {J} [category J] {V W : J ⥤ SemiNormedGroup} (f g : V ⟶ W) : J ⥤ SemiNormedGroup :=
{ obj := λ X, of ((f.app X).equalizer (g.app X)),
  map := λ X Y φ, equalizer.map (V.map φ) (W.map φ) (f.naturality _) (g.naturality _),
  map_id' := λ X, by simp only [category_theory.functor.map_id]; exact normed_group_hom.equalizer.map_id,
  map_comp' := λ X Y Z φ ψ, begin
    simp only [functor.map_comp],
    exact (map_comp_map _ _ _ _).symm
  end }

@[simps]
def map_nat {J} [category J] {V₁ V₂ W₁ W₂ : J ⥤ SemiNormedGroup}
  {f₁ f₂ g₁ g₂} (φ : V₁ ⟶ V₂) (ψ : W₁ ⟶ W₂)
  (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ) :
  equalizer.F f₁ g₁ ⟶ equalizer.F f₂ g₂ :=
{ app := λ X, equalizer.map (φ.app X) (ψ.app X)
    (by rw [← nat_trans.comp_app, ← nat_trans.comp_app, hf])
    (by rw [← nat_trans.comp_app, ← nat_trans.comp_app, hg]),
  naturality' := λ X Y α, by simp only [equalizer.F_map, map_comp_map, nat_trans.naturality] }

lemma map_nat_comp_map_nat {J} [category J] {V₁ V₂ V₃ W₁ W₂ W₃ : J ⥤ SemiNormedGroup}
  {f₁ f₂ f₃ g₁ g₂ g₃} {φ : V₁ ⟶ V₂} {ψ : W₁ ⟶ W₂} {φ' : V₂ ⟶ V₃} {ψ' : W₂ ⟶ W₃}
  (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ)
  (hf' : φ' ≫ f₃ = f₂ ≫ ψ') (hg' : φ' ≫ g₃ = g₂ ≫ ψ') :
  map_nat φ ψ hf hg ≫ map_nat φ' ψ' hf' hg' =
  map_nat (φ ≫ φ') (ψ ≫ ψ') (comm_sq₂ hf hf') (comm_sq₂ hg hg') :=
by { ext, refl }

lemma map_nat_id {J} [category J] {V W : J ⥤ SemiNormedGroup} (f g : V ⟶ W) :
  map_nat (𝟙 V) (𝟙 W) (show 𝟙 V ≫ f = f ≫ 𝟙 W, by simp) (show 𝟙 V ≫ g = g ≫ 𝟙 W, by simp) = 𝟙 _ :=
by { ext, refl }

end equalizer
end SemiNormedGroup

universe variable u
variables (r : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
variables (M M₁ M₂ M₃ : ProFiltPseuNormGrpWithTinv.{u} r')
variables (c c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℝ≥0) (l m n : ℕ)
variables (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)

def CLCTinv (r : ℝ≥0) (V : SemiNormedGroup)
  [normed_with_aut r V] [fact (0 < r)] {A B : Profiniteᵒᵖ} (f g : A ⟶ B) :
  SemiNormedGroup :=
SemiNormedGroup.of $ normed_group_hom.equalizer
  ((CLC V).map f)
  ((CLC V).map g ≫ (CLC.T_inv r V).app B)

namespace CLCTinv

def ι (r : ℝ≥0) (V : SemiNormedGroup)
  [normed_with_aut r V] [fact (0 < r)] {A B : Profiniteᵒᵖ} (f g : A ⟶ B) :
  CLCTinv r V f g ⟶ (CLC V).obj A :=
SemiNormedGroup.equalizer.ι _ _

lemma ι_range (r : ℝ≥0) (V : SemiNormedGroup)
  [normed_with_aut r V] [fact (0 < r)] {A B : Profiniteᵒᵖ} (f g : A ⟶ B) :
  (ι r V f g).range =
    normed_group_hom.ker ((CLC V).map f - ((CLC V).map g ≫ (CLC.T_inv r V).app B)) :=
SemiNormedGroup.equalizer.ι_range _ _

lemma ι_range' (r : ℝ≥0) (V : SemiNormedGroup)
  [normed_with_aut r V] [fact (0 < r)] {A B : Profiniteᵒᵖ} (f g : A ⟶ B) :
  (ι r V f g).range =
    normed_group_hom.ker (((CLC V).map g ≫ (CLC.T_inv r V).app B) - (CLC V).map f) :=
SemiNormedGroup.equalizer.ι_range' _ _

def map {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂) (h₁ : ϕ ≫ f₂ = f₁ ≫ ψ) (h₂ : ϕ ≫ g₂ = g₁ ≫ ψ) :
  CLCTinv r V f₁ g₁ ⟶ CLCTinv r V f₂ g₂ :=
SemiNormedGroup.equalizer.map ((CLC V).map ϕ) ((CLC V).map ψ)
  (by rw [← functor.map_comp, ← functor.map_comp, h₁]) $
by rw [← category.assoc, ← functor.map_comp, h₂, functor.map_comp,
  category.assoc, (CLC.T_inv _ _).naturality, category.assoc]

def map_comp_ι {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂) (h₁ : ϕ ≫ f₂ = f₁ ≫ ψ) (h₂ : ϕ ≫ g₂ = g₁ ≫ ψ) :
  map r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂ ≫ ι r V _ _ = ι _ _ _ _ ≫ (CLC V).map ϕ :=
normed_group_hom.equalizer.map_ι _ _

lemma map_norm_noninc {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂) (h₁ h₂) :
  (CLCTinv.map r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂).norm_noninc :=
equalizer.map_norm_noninc _ _ $ CLC.map_norm_noninc _ _

lemma norm_map_le {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂) (h₁ h₂) (C : ℝ≥0)
  (H : ∥SemiNormedGroup.equalizer.ι
         ((CLC V).map f₁)
         ((CLC V).map g₁ ≫ (CLC.T_inv r V).app B₁) ≫
       (CLC V).map ϕ∥ ≤ C) :
  ∥CLCTinv.map r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂∥ ≤ C :=
SemiNormedGroup.equalizer.norm_map_le _ _ C H

@[simp] lemma map_id {A B : Profiniteᵒᵖ} (f g : A ⟶ B) :
  map r V f g f g (𝟙 A) (𝟙 B) rfl rfl = 𝟙 _ :=
begin
  simp only [map, SemiNormedGroup.equalizer.map, category_theory.functor.map_id],
  exact equalizer.map_id,
end

lemma map_comp {A₁ A₂ A₃ B₁ B₂ B₃ : Profiniteᵒᵖ}
  {f₁ g₁ : A₁ ⟶ B₁} {f₂ g₂ : A₂ ⟶ B₂} {f₃ g₃ : A₃ ⟶ B₃}
  (ϕ₁ : A₁ ⟶ A₂) (ϕ₂ : A₂ ⟶ A₃) (ψ₁ : B₁ ⟶ B₂) (ψ₂ : B₂ ⟶ B₃)
  (h1 h2 h3 h4 h5 h6) :
  CLCTinv.map r V f₁ g₁ f₃ g₃ (ϕ₁ ≫ ϕ₂) (ψ₁ ≫ ψ₂) h1 h2 =
  CLCTinv.map r V f₁ g₁ f₂ g₂ ϕ₁ ψ₁ h3 h4 ≫
  CLCTinv.map r V f₂ g₂ f₃ g₃ ϕ₂ ψ₂ h5 h6 :=
begin
  simp only [map, SemiNormedGroup.equalizer.map, category_theory.functor.map_comp],
  exact (equalizer.map_comp_map _ _ _ _).symm,
end

lemma map_comp_map {A₁ A₂ A₃ B₁ B₂ B₃ : Profiniteᵒᵖ}
  {f₁ g₁ : A₁ ⟶ B₁} {f₂ g₂ : A₂ ⟶ B₂} {f₃ g₃ : A₃ ⟶ B₃}
  (ϕ₁ : A₁ ⟶ A₂) (ϕ₂ : A₂ ⟶ A₃) (ψ₁ : B₁ ⟶ B₂) (ψ₂ : B₂ ⟶ B₃)
  (h₁ h₂ h₃ h₄) :
  CLCTinv.map r V f₁ g₁ f₂ g₂ ϕ₁ ψ₁ h₁ h₂ ≫
  CLCTinv.map r V f₂ g₂ f₃ g₃ ϕ₂ ψ₂ h₃ h₄ =
  CLCTinv.map r V f₁ g₁ f₃ g₃ (ϕ₁ ≫ ϕ₂) (ψ₁ ≫ ψ₂) (comm_sq₂ h₁ h₃) (comm_sq₂ h₂ h₄) :=
(map_comp _ _ _ _ _ _ _ _ _ _ _ _).symm

@[simps]
def map_iso {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ≅ A₂) (ψ : B₁ ≅ B₂) (h₁ : ϕ.hom ≫ f₂ = f₁ ≫ ψ.hom) (h₂ : ϕ.hom ≫ g₂ = g₁ ≫ ψ.hom) :
  CLCTinv r V f₁ g₁ ≅ CLCTinv r V f₂ g₂ :=
{ hom := map r V f₁ g₁ f₂ g₂ ϕ.hom ψ.hom h₁ h₂,
  inv := map r V f₂ g₂ f₁ g₁ ϕ.inv ψ.inv
    (by rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, h₁])
    (by rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, h₂]),
  hom_inv_id' := by { simp only [map_comp_map, iso.hom_inv_id], apply map_id },
  inv_hom_id' := by { simp only [map_comp_map, iso.inv_hom_id], apply map_id } }

lemma map_iso_isometry {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ≅ A₂) (ψ : B₁ ≅ B₂) (h₁ : ϕ.hom ≫ f₂ = f₁ ≫ ψ.hom) (h₂ : ϕ.hom ≫ g₂ = g₁ ≫ ψ.hom) :
  isometry (map_iso r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂).hom :=
begin
  apply SemiNormedGroup.iso_isometry_of_norm_noninc;
  apply map_norm_noninc
end

@[simps]
protected def F {J} [category J] (r : ℝ≥0) (V : SemiNormedGroup)
  [normed_with_aut r V] [fact (0 < r)] {A B : J ⥤ Profiniteᵒᵖ} (f g : A ⟶ B) :
  J ⥤ SemiNormedGroup :=
{ obj := λ X, CLCTinv r V (f.app X) (g.app X),
  map := λ X Y φ, map _ _ _ _ _ _ (A.map φ) (B.map φ) (f.naturality _) (g.naturality _),
  map_id' := λ X, by simp only [category_theory.functor.map_id]; apply map_id,
  map_comp' := λ X Y Z φ ψ, by simp only [functor.map_comp]; apply map_comp }

theorem F_def {J} [category J] (r : ℝ≥0) (V : SemiNormedGroup)
  [normed_with_aut r V] [fact (0 < r)] {A B : J ⥤ Profiniteᵒᵖ} (f g : A ⟶ B) :
  CLCTinv.F r V f g = SemiNormedGroup.equalizer.F
    (whisker_right f (CLC V))
    (whisker_right g (CLC V) ≫ whisker_left B (CLC.T_inv r V)) := rfl

@[simps]
def map_nat {J} [category J] {A₁ B₁ A₂ B₂ : J ⥤ Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂) (h₁ : ϕ ≫ f₂ = f₁ ≫ ψ) (h₂ : ϕ ≫ g₂ = g₁ ≫ ψ) :
  CLCTinv.F r V f₁ g₁ ⟶ CLCTinv.F r V f₂ g₂ :=
{ app := λ X, map _ _ _ _ _ _ (ϕ.app X) (ψ.app X)
    (by rw [← nat_trans.comp_app, h₁, nat_trans.comp_app])
    (by rw [← nat_trans.comp_app, h₂, nat_trans.comp_app]),
  naturality' := λ X Y α, by simp only [CLCTinv.F_map, map_comp_map, ϕ.naturality, ψ.naturality] }

theorem map_nat_def {J} [category J] {A₁ B₁ A₂ B₂ : J ⥤ Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂) (h₁ : ϕ ≫ f₂ = f₁ ≫ ψ) (h₂ : ϕ ≫ g₂ = g₁ ≫ ψ) :
  map_nat r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂ = begin
    dsimp only [F_def],
    refine SemiNormedGroup.equalizer.map_nat
      (whisker_right ϕ (CLC V))
      (whisker_right ψ (CLC V))
      (by rw [← whisker_right_comp, ← whisker_right_comp, h₁])
      (comm_sq₂ _ _).symm,
    { exact whisker_right ψ _ },
    { rw [← whisker_right_comp, ← whisker_right_comp, h₂] },
    ext x : 2,
    simp only [nat_trans.comp_app, whisker_left_app, whisker_right_app,
      (CLC.T_inv _ _).naturality],
  end := rfl
.

-- @[simps]
def map_nat_iso {J} [category J] {A₁ B₁ A₂ B₂ : J ⥤ Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
  (ϕ : A₁ ≅ A₂) (ψ : B₁ ≅ B₂) (h₁ : ϕ.hom ≫ f₂ = f₁ ≫ ψ.hom) (h₂ : ϕ.hom ≫ g₂ = g₁ ≫ ψ.hom) :
  CLCTinv.F r V f₁ g₁ ≅ CLCTinv.F r V f₂ g₂ :=
{ hom := map_nat r V f₁ g₁ f₂ g₂ ϕ.hom ψ.hom h₁ h₂,
  inv := map_nat r V f₂ g₂ f₁ g₁ ϕ.inv ψ.inv
    (by rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, h₁])
    (by rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, h₂]),
  hom_inv_id' :=
  begin
    simp only [map_nat_def, _root_.id, SemiNormedGroup.equalizer.map_nat_comp_map_nat,
      ← whisker_right_comp, iso.hom_inv_id, whisker_right_id', SemiNormedGroup.equalizer.map_nat_id],
    refl
  end,
  inv_hom_id' :=
  begin
    simp only [map_nat_def, _root_.id, SemiNormedGroup.equalizer.map_nat_comp_map_nat,
      ← whisker_right_comp, iso.inv_hom_id, whisker_right_id', SemiNormedGroup.equalizer.map_nat_id],
    refl
  end, }

end CLCTinv

lemma aux (r' c c₂ : ℝ≥0) [r1 : fact (r' ≤ 1)] [h : fact (c₂ ≤ r' * c)] : fact (c₂ ≤ c) :=
⟨h.1.trans $ (mul_le_mul' r1.1 le_rfl).trans (by simp)⟩

@[simps obj]
def CLCFPTinv₂ (r : ℝ≥0) (V : SemiNormedGroup)
  (r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [r1 : fact (r' ≤ 1)] [normed_with_aut r V]
  (c c₂ : ℝ≥0) [fact (c₂ ≤ r' * c)] (n : ℕ) : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup :=
by haveI : fact (c₂ ≤ c) := aux r' c c₂; exact
CLCTinv.F r V
  (nat_trans.op (FiltrationPow.Tinv r' c₂ c n))
  (nat_trans.op (FiltrationPow.cast_le r' c₂ c n))

theorem CLCFPTinv₂_def (r : ℝ≥0) (V : SemiNormedGroup)
  (r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [r1 : fact (r' ≤ 1)] [normed_with_aut r V]
  (c c₂ : ℝ≥0) [fact (c₂ ≤ r' * c)] (n : ℕ) :
  CLCFPTinv₂ r V r' c c₂ n = SemiNormedGroup.equalizer.F
    (CLCFP.Tinv V r' c c₂ n)
    (@CLCFP.res V r' c c₂ n (aux r' c c₂) ≫ CLCFP.T_inv r V r' c₂ n) := rfl

instance CLCFPTinv₂.separated_space [fact (c₂ ≤ r' * c₁)] (M) :
  separated_space ((CLCFPTinv₂ r V r' c₁ c₂ n).obj M) :=
begin
  rw separated_iff_t2,
  refine @subtype.t2_space _ _ (id _) (id _),
  rw ← separated_iff_t2,
  apply uniform_space.completion.separated_space
end

instance CLCFPTinv₂.complete_space [fact (c₂ ≤ r' * c₁)] (M) :
  complete_space ((CLCFPTinv₂ r V r' c₁ c₂ n).obj M) :=
begin
  refine @is_closed.complete_space_coe _ (id _) (id _) _ _,
  { apply uniform_space.completion.complete_space },
  { refine is_closed_eq _ continuous_const,
    apply normed_group_hom.continuous }
end

/-- The functor that sends `M` and `c` to `V-hat((filtration M c)^n)^{T⁻¹}`,
defined by taking `T⁻¹`-invariants for two different actions by `T⁻¹`:

* The first comes from the action of `T⁻¹` on `M`.
* The second comes from the action of `T⁻¹` on `V`.

We take the equalizer of those two actions.

See the lines just above Definition 9.3 of [Analytic]. -/
def CLCFPTinv (r : ℝ≥0) (V : SemiNormedGroup) (r' : ℝ≥0)
  (c : ℝ≥0) (n : ℕ) [normed_with_aut r V] [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup :=
CLCFPTinv₂ r V r' c (r' * c) n

namespace CLCFPTinv₂

lemma map_norm_noninc [fact (c₂ ≤ r' * c)] [fact (c₂ ≤ c)]
  {M₁ M₂} (f : M₁ ⟶ M₂) : ((CLCFPTinv₂ r V r' c c₂ n).map f).norm_noninc :=
CLCTinv.map_norm_noninc _ _ _ _ _ _ _ _ _ _

def res [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)] [fact (c₄ ≤ r' * c₃)] [fact (c₄ ≤ c₃)]
  [fact (c₃ ≤ c₁)] [fact (c₄ ≤ c₂)] : CLCFPTinv₂ r V r' c₁ c₂ n ⟶ CLCFPTinv₂ r V r' c₃ c₄ n :=
CLCTinv.map_nat r V _ _ _ _
  (nat_trans.op (FiltrationPow.cast_le _ c₃ c₁ n))
  (nat_trans.op (FiltrationPow.cast_le _ c₄ c₂ n)) rfl rfl

@[simp] lemma res_refl [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)] : res r V r' c₁ c₂ c₁ c₂ n = 𝟙 _ :=
by { simp only [res, FiltrationPow.cast_le_refl, nat_trans.op_id], ext x : 2, apply CLCTinv.map_id }

lemma res_comp_res
  [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)]
  [fact (c₄ ≤ r' * c₃)] [fact (c₄ ≤ c₃)]
  [fact (c₆ ≤ r' * c₅)] [fact (c₆ ≤ c₅)]
  [fact (c₃ ≤ c₁)] [fact (c₄ ≤ c₂)]
  [fact (c₅ ≤ c₃)] [fact (c₆ ≤ c₄)]
  [fact (c₅ ≤ c₁)] [fact (c₆ ≤ c₂)] :
  res r V r' c₁ c₂ c₃ c₄ n ≫ res r V r' c₃ c₄ c₅ c₆ n = res r V r' c₁ c₂ c₅ c₆ n :=
begin
  ext x : 2, simp only [res, nat_trans.comp_app],
  exact (CLCTinv.map_comp _ _ _ _ _ _ _ _ _ _ _ _).symm
end

lemma res_norm_noninc {_ : fact (c₂ ≤ r' * c₁)} {_ : fact (c₂ ≤ c₁)}
  {_ : fact (c₄ ≤ r' * c₃)} {_ : fact (c₄ ≤ c₃)} {_ : fact (c₃ ≤ c₁)} {_ : fact (c₄ ≤ c₂)} (M) :
  ((res r V r' c₁ c₂ c₃ c₄ n).app M).norm_noninc :=
CLCTinv.map_norm_noninc _ _ _ _ _ _ _ _ _ _

lemma norm_res_le [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)] [fact (c₄ ≤ r' * c₃)] [fact (c₄ ≤ c₃)]
  [fact (c₃ ≤ c₁)] [fact (c₄ ≤ c₂)] (h₂₃ : c₂ = c₃) (M) :
  ∥(res r V r' c₁ c₂ c₃ c₄ n).app M∥ ≤ r :=
begin
  apply CLCTinv.norm_map_le,
  rw [← category.comp_id ((CLC V).map ((nat_trans.op (FiltrationPow.cast_le r' c₃ c₁ n)).app M))],
  have := nat_trans.congr_app (CLC.T r V).inv_hom_id ((FiltrationPow r' c₃ n).op.obj M),
  dsimp only [nat_trans.id_app] at this,
  rw [← this, CLC.T_inv_eq, nat_trans.comp_app, ← category.assoc ((CLC V).map _)],
  unfreezingI { subst c₃ },
  rw [← SemiNormedGroup.equalizer.condition_assoc, ← category.assoc],
  refine normed_group_hom.norm_comp_le_of_le' 1 r r (mul_one ↑r).symm _ _,
  { apply CLC.norm_T_le },
  { apply norm_noninc.norm_noninc_iff_norm_le_one.1,
    exact (CLC.map_norm_noninc V _).comp equalizer.ι_norm_noninc }
end

end CLCFPTinv₂

namespace CLCFPTinv

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((CLCFPTinv r V r' c n).map f).norm_noninc :=
CLCFPTinv₂.map_norm_noninc _ _ _ _ _ _ _

def res [fact (c₂ ≤ c₁)] : CLCFPTinv r V r' c₁ n ⟶ CLCFPTinv r V r' c₂ n :=
CLCFPTinv₂.res r V r' c₁ _ c₂ _ n

@[simp] lemma res_refl : res r V r' c₁ c₁ n = 𝟙 _ :=
CLCFPTinv₂.res_refl _ _ _ _ _ _

lemma res_comp_res [fact (c₃ ≤ c₁)] [fact (c₅ ≤ c₃)] [fact (c₅ ≤ c₁)] :
  res r V r' c₁ c₃ n ≫ res r V r' c₃ c₅ n = res r V r' c₁ c₅ n :=
CLCFPTinv₂.res_comp_res _ _ _ _ _ _ _ _ _ _

lemma res_norm_noninc {_ : fact (c₂ ≤ c₁)} (M) :
  ((res r V r' c₁ c₂ n).app M).norm_noninc :=
CLCFPTinv₂.res_norm_noninc r V r' _ _ _ _ _ _

lemma norm_res_le [fact (c₂ ≤ c₁)] [fact (c₂ ≤ r' * c₁)] (M) :
  ∥(res r V r' c₁ c₂ n).app M∥ ≤ r :=
begin
  rw ← res_comp_res r V r' c₁ (r' * c₁) c₂,
  refine norm_comp_le_of_le' _ _ _ (one_mul ↑r).symm _ (CLCFPTinv₂.norm_res_le r V r' _ _ _ _ n rfl M),
  apply norm_noninc.norm_noninc_iff_norm_le_one.1,
  exact CLCTinv.map_norm_noninc r V _ _ _ _ _ _ _ _
end

lemma norm_res_le_pow (N : ℕ) [fact (c₂ ≤ c₁)] [h : fact (c₂ ≤ r' ^ N * c₁)] (M) :
  ∥(res r V r' c₁ c₂ n).app M∥ ≤ (r ^ N) :=
begin
  unfreezingI { induction N with N ih generalizing c₁ c₂ },
  { rw pow_zero,
    apply norm_noninc.norm_noninc_iff_norm_le_one.1,
    exact CLCTinv.map_norm_noninc r V _ _ _ _ _ _ _ _ },
  haveI : fact (c₂ ≤ r' ^ N * c₁) := nnreal.fact_le_pow_mul_of_le_pow_succ_mul _ _ _,
  rw [pow_succ, mul_assoc] at h, resetI,
  rw [← res_comp_res r V r' c₁ (r' ^ N * c₁) c₂],
  exact norm_comp_le_of_le' _ _ _ (pow_succ _ _) (norm_res_le r V r' _ _ n M) (ih _ _)
end

end CLCFPTinv

namespace breen_deligne

open CLCFPTinv

variables (M) {l m n}

namespace universal_map

variables (ϕ ψ : universal_map m n)

def eval_CLCFPTinv₂
  [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂] :
  CLCFPTinv₂ r V r' c₁ c₂ n ⟶ CLCFPTinv₂ r V r' c₃ c₄ m :=
begin
  dsimp only [CLCFPTinv₂_def],
  refine SemiNormedGroup.equalizer.map_nat (ϕ.eval_CLCFP _ _ _ _) (ϕ.eval_CLCFP _ _ _ _)
    (Tinv_comp_eval_CLCFP V r' c₁ c₂ c₃ c₄ ϕ).symm _,
  haveI : fact (c₂ ≤ c₁) := aux r' _ _, haveI : fact (c₄ ≤ c₃) := aux r' _ _,
  have h₁ := res_comp_eval_CLCFP V r' c₁ c₂ c₃ c₄ ϕ,
  have h₂ := T_inv_comp_eval_CLCFP r V r' c₂ c₄ ϕ,
  have := comm_sq₂ h₁ h₂,
  exact this.symm
end

@[simp] lemma eval_CLCFPTinv₂_zero
  [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)] :
  (0 : universal_map m n).eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ = 0 :=
by { simp only [eval_CLCFPTinv₂, eval_CLCFP_zero], ext, refl }

@[simp] lemma eval_CLCFPTinv₂_add
  [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂]
  [ψ.suitable c₃ c₁] [ψ.suitable c₄ c₂] :
  (ϕ + ψ : universal_map m n).eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ =
  ϕ.eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ + ψ.eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ :=
by { simp only [eval_CLCFPTinv₂, eval_CLCFP_add], ext, refl }

@[simp] lemma eval_CLCFPTinv₂_sub
  [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂]
  [ψ.suitable c₃ c₁] [ψ.suitable c₄ c₂] :
  (ϕ - ψ : universal_map m n).eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ =
  ϕ.eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ - ψ.eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ :=
by { simp only [eval_CLCFPTinv₂, eval_CLCFP_sub], ext, refl }

lemma eval_CLCFPTinv₂_comp {l m n : FreeMat} (f : l ⟶ m) (g : m ⟶ n)
  [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)] [fact (c₆ ≤ r' * c₅)]
  [f.suitable c₅ c₃] [f.suitable c₆ c₄] [g.suitable c₃ c₁] [g.suitable c₄ c₂] :
  @eval_CLCFPTinv₂ r V _ _ r' _ _ c₁ c₂ c₅ c₆ _ _ (f ≫ g)
    _ _ (suitable.comp c₃) (suitable.comp c₄) =
  g.eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ ≫ f.eval_CLCFPTinv₂ r V r' c₃ c₄ c₅ c₆ :=
begin
  dsimp only [eval_CLCFPTinv₂, CLCFPTinv₂_def], delta id,
  simp only [SemiNormedGroup.equalizer.map_nat_comp_map_nat],
  generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8,
  revert h5 h6 h7 h8, resetI,
  have H1 : eval_CLCFP V r' c₁ c₅ (f ≫ g) = eval_CLCFP V r' c₁ c₃ g ≫ eval_CLCFP V r' c₃ c₅ f :=
    eval_CLCFP_comp V r' c₁ c₃ c₅ g f,
  have H2 : eval_CLCFP V r' c₂ c₆ (f ≫ g) = eval_CLCFP V r' c₂ c₄ g ≫ eval_CLCFP V r' c₄ c₆ f :=
    eval_CLCFP_comp V r' c₂ c₄ c₆ g f,
  rw [H1, H2],
  intros, refl,
end

lemma res_comp_eval_CLCFPTinv₂
  [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [fact (c₆ ≤ r' * c₅)] [fact (c₈ ≤ r' * c₇)]
  [fact (c₂ ≤ c₁)] [fact (c₃ ≤ c₁)] [fact (c₄ ≤ c₂)] [fact (c₄ ≤ c₃)]
  [fact (c₆ ≤ c₅)] [fact (c₇ ≤ c₅)] [fact (c₈ ≤ c₆)] [fact (c₈ ≤ c₇)]
  [ϕ.suitable c₅ c₁] [ϕ.suitable c₆ c₂]
  [ϕ.suitable c₇ c₃] [ϕ.suitable c₈ c₄] :
  CLCFPTinv₂.res r V r' c₁ c₂ c₃ c₄ n ≫ ϕ.eval_CLCFPTinv₂ r V r' c₃ c₄ c₇ c₈ =
    ϕ.eval_CLCFPTinv₂ r V r' c₁ c₂ c₅ c₆ ≫ CLCFPTinv₂.res r V r' c₅ c₆ c₇ c₈ m :=
begin
  dsimp only [CLCFPTinv₂.res, eval_CLCFPTinv₂, CLCFPTinv₂_def, CLCTinv.map_nat_def], delta id,
  simp only [SemiNormedGroup.equalizer.map_nat_comp_map_nat],
  congr' 1; { simp only [← CLCFP.res_def], apply res_comp_eval_CLCFP },
end

lemma norm_eval_CLCFPTinv₂_le [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂] (N : ℕ) (h : ϕ.bound_by N) (M) :
  ∥(ϕ.eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄).app M∥ ≤ N :=
begin
  apply SemiNormedGroup.equalizer.norm_map_le,
  refine normed_group_hom.norm_comp_le_of_le' _ _ _ (mul_one _).symm _ _,
  { apply norm_eval_CLCFP_le, exact h },
  { apply norm_noninc.norm_noninc_iff_norm_le_one.1,
    exact equalizer.ι_norm_noninc }
end

def eval_CLCFPTinv [ϕ.suitable c₂ c₁] :
  CLCFPTinv r V r' c₁ n ⟶ CLCFPTinv r V r' c₂ m :=
ϕ.eval_CLCFPTinv₂ r V r' c₁ _ c₂ _

lemma eval_CLCFPTinv_def [ϕ.suitable c₂ c₁] :
  ϕ.eval_CLCFPTinv r V r' c₁ c₂ = ϕ.eval_CLCFPTinv₂ r V r' c₁ _ c₂ _ := rfl

@[simp] lemma eval_CLCFPTinv_zero :
  (0 : universal_map m n).eval_CLCFPTinv r V r' c₁ c₂ = 0 :=
by apply eval_CLCFPTinv₂_zero

@[simp] lemma eval_CLCFPTinv_add [ϕ.suitable c₂ c₁] [ψ.suitable c₂ c₁] :
  (ϕ + ψ : universal_map m n).eval_CLCFPTinv r V r' c₁ c₂ =
  ϕ.eval_CLCFPTinv r V r' c₁ c₂ + ψ.eval_CLCFPTinv r V r' c₁ c₂ :=
eval_CLCFPTinv₂_add _ _ _ _ _ _ _ _ _

@[simp] lemma eval_CLCFPTinv_sub [ϕ.suitable c₂ c₁] [ψ.suitable c₂ c₁] :
  (ϕ - ψ : universal_map m n).eval_CLCFPTinv r V r' c₁ c₂ =
  ϕ.eval_CLCFPTinv r V r' c₁ c₂ - ψ.eval_CLCFPTinv r V r' c₁ c₂ :=
eval_CLCFPTinv₂_sub _ _ _ _ _ _ _ _ _

lemma eval_CLCFPTinv_comp {l m n : FreeMat} (f : l ⟶ m) (g : m ⟶ n)
  [hg : g.suitable c₂ c₁] [hf : f.suitable c₃ c₂] :
  @eval_CLCFPTinv r V _ _ r' _ _ c₁ c₃ _ _ (f ≫ g) (suitable.comp c₂) =
    g.eval_CLCFPTinv r V r' c₁ c₂ ≫ f.eval_CLCFPTinv r V r' c₂ c₃ :=
by apply eval_CLCFPTinv₂_comp

lemma res_comp_eval_CLCFPTinv
  [fact (c₂ ≤ c₁)] [ϕ.suitable c₄ c₂] [ϕ.suitable c₃ c₁] [fact (c₄ ≤ c₃)] :
  res r V r' c₁ c₂ n ≫ ϕ.eval_CLCFPTinv r V r' c₂ c₄ =
    ϕ.eval_CLCFPTinv r V r' c₁ c₃ ≫ res r V r' c₃ c₄ m :=
by apply res_comp_eval_CLCFPTinv₂

lemma res_comp_eval_CLCFPTinv_absorb
  [fact (c₂ ≤ c₁)] [hϕ : ϕ.suitable c₃ c₂] :
  res r V r' c₁ c₂ n ≫ ϕ.eval_CLCFPTinv r V r' c₂ c₃ =
    @eval_CLCFPTinv r V _ _ r' _ _ c₁ c₃ _ _ ϕ (hϕ.le _ _ _ _ le_rfl (fact.out _)) :=
by rw [@res_comp_eval_CLCFPTinv r V _ _ r' _ _ c₁ c₂ c₃ c₃ _ _ ϕ
      (_root_.id _) (_root_.id _) (_root_.id _) (_root_.id _),
    res_refl, category.comp_id]

lemma eval_CLCFPTinv_comp_res_absorb
  {_: fact (c₃ ≤ c₂)} [hϕ : ϕ.suitable c₂ c₁] :
  ϕ.eval_CLCFPTinv r V r' c₁ c₂ ≫ res r V r' c₂ c₃ m =
    @eval_CLCFPTinv r V _ _ r' _ _ c₁ c₃ _ _ ϕ (hϕ.le _ _ _ _ (fact.out _) le_rfl) :=
by rw [← @res_comp_eval_CLCFPTinv r V _ _ r' _ _ c₁ c₁ c₂ c₃ _ _ ϕ
      (_root_.id _) (_root_.id _) (_root_.id _) (_root_.id _),
    res_refl, category.id_comp]

lemma norm_eval_CLCFPTinv_le [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₂ c₁]
  (N : ℕ) (h : ϕ.bound_by N) (M) :
  ∥(ϕ.eval_CLCFPTinv r V r' c₁ c₂).app M∥ ≤ N :=
norm_eval_CLCFPTinv₂_le r V r' _ _ _ _ _ N h M

lemma eval_CLCFPTinv_norm_noninc [normed_with_aut r V] [fact (0 < r)]
  [h : ϕ.very_suitable r r' c₂ c₁] (M) :
  ((ϕ.eval_CLCFPTinv r V r' c₁ c₂).app M).norm_noninc :=
begin
  apply norm_noninc.norm_noninc_iff_norm_le_one.2,
  have h' := h,
  unfreezingI { rcases h with ⟨N, k, c', hN, hϕ, hr, H⟩ },
  haveI : fact (c' ≤ c₁) := ⟨H.trans $ fact.out _⟩,
  have aux := res_comp_eval_CLCFPTinv r V r' c₁ c' c₂ c₂ ϕ,
  rw [res_refl, category.comp_id] at aux,
  rw ← aux,
  refine le_trans _ hr,
  rw mul_comm,
  apply normed_group_hom.norm_comp_le_of_le,
  { apply_mod_cast norm_eval_CLCFPTinv_le, exact hN },
  { haveI : fact (c' ≤ r' ^ k * c₁) := ⟨H⟩,
    rw nnreal.coe_pow,
    apply norm_res_le_pow },
end

end universal_map

end breen_deligne

attribute [irreducible] CLCFPTinv₂ CLCFPTinv₂.res
  breen_deligne.universal_map.eval_CLCFPTinv₂
