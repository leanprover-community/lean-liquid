import pseudo_normed_group.category.ProFiltPseuNormGrp

universe variables u

open category_theory
open_locale nnreal

noncomputable theory

local attribute [instance] type_pow

/-- The bundled category whose objects are `profinitely_filtered_pseudo_normed_group`s
equipped (this is the `₁`) with exhaustive filtrations and strict morphisms. -/
structure ProFiltPseuNormGrp₁ : Type (u+1) :=
(M : Type u)
[str : profinitely_filtered_pseudo_normed_group M]
(exhaustive' : ∀ m : M, ∃ c, m ∈ pseudo_normed_group.filtration M c)

namespace ProFiltPseuNormGrp₁

instance : has_coe_to_sort ProFiltPseuNormGrp₁ Type* := ⟨λ M, M.M⟩
instance (M : ProFiltPseuNormGrp₁) : profinitely_filtered_pseudo_normed_group M := M.str

lemma exhaustive (M : ProFiltPseuNormGrp₁) (m : M) :
  ∃ c, m ∈ pseudo_normed_group.filtration M c := M.exhaustive' m

instance : large_category ProFiltPseuNormGrp₁.{u} :=
{ hom := λ A B, strict_comphaus_filtered_pseudo_normed_group_hom A B,
  id := λ A, strict_comphaus_filtered_pseudo_normed_group_hom.id,
  comp := λ A B C f g, g.comp f }

def enlarging_functor : ProFiltPseuNormGrp₁ ⥤ ProFiltPseuNormGrp :=
{ obj := λ M, ProFiltPseuNormGrp.of M,
  map := λ M₁ M₂ f, f.to_chfpsng_hom }

instance : concrete_category ProFiltPseuNormGrp₁.{u} :=
{ forget :=
  { obj := λ M, M.M,
    map := λ A B f, f },
  forget_faithful := ⟨⟩ } .

/-- The forgetful functor from groups filtered by profinite spaces to
groups filtered by compact Hausdorff spaces. -/
def _root_.PFPNG₁_to_CHFPNG₁ₗₑ : ProFiltPseuNormGrp₁.{u} ⥤ CompHausFiltPseuNormGrp₁.{u} :=
{ obj := λ M,
  { M := M,
    exhaustive' := M.exhaustive },
  map := λ A B f, f }

def limit_cone {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrp₁.{u}) :
  limits.cone K :=
{ X :=
  { M := (CompHausFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNG₁_to_CHFPNG₁ₗₑ)).X,
    str :=
    { continuous_add' := comphaus_filtered_pseudo_normed_group.continuous_add',
      continuous_neg' := comphaus_filtered_pseudo_normed_group.continuous_neg',
      continuous_cast_le := comphaus_filtered_pseudo_normed_group.continuous_cast_le,
      td := begin
        intro c,
        let E := (CompHausFiltPseuNormGrp₁.cone_point_type.filt_homeo (K ⋙ PFPNG₁_to_CHFPNG₁ₗₑ) c),
        haveI : totally_disconnected_space
          (CompHausFiltPseuNormGrp₁.cone_point_type_filt (K ⋙ PFPNG₁_to_CHFPNG₁ₗₑ) c) :=
        begin
          dsimp [CompHausFiltPseuNormGrp₁.cone_point_type_filt],
          apply_instance,
        end,
        apply E.symm.totally_disconnected_space,
      end,
      ..(infer_instance : pseudo_normed_group _) },
    exhaustive' :=  CompHausFiltPseuNormGrp₁.exhaustive _ },
  π :=
  { app := λ j, (CompHausFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNG₁_to_CHFPNG₁ₗₑ)).π.app j,
    naturality' := (CompHausFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNG₁_to_CHFPNG₁ₗₑ)).π.naturality } }

instance {J : Type u} [small_category J] : creates_limits_of_shape J PFPNG₁_to_CHFPNG₁ₗₑ :=
{ creates_limit := λ K,
  { reflects := λ C hC,
    { lift := λ S, hC.lift (PFPNG₁_to_CHFPNG₁ₗₑ.map_cone S),
      fac' := λ S j, hC.fac _ _,
      uniq' := λ S m h, hC.uniq (PFPNG₁_to_CHFPNG₁ₗₑ.map_cone S) m h },
    lifts := λ C hC,
    { lifted_cone := limit_cone _,
      valid_lift :=
        (CompHausFiltPseuNormGrp₁.limit_cone_is_limit (K ⋙ PFPNG₁_to_CHFPNG₁ₗₑ)).unique_up_to_iso hC } } }

instance : creates_limits PFPNG₁_to_CHFPNG₁ₗₑ := ⟨⟩

def limit_cone_is_limit {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrp₁.{u}) :
  limits.is_limit (limit_cone K) :=
limits.is_limit_of_reflects PFPNG₁_to_CHFPNG₁ₗₑ (CompHausFiltPseuNormGrp₁.limit_cone_is_limit _)

instance : limits.has_limits ProFiltPseuNormGrp₁.{u} :=
has_limits_of_has_limits_creates_limits PFPNG₁_to_CHFPNG₁ₗₑ

lemma eq_of_π_eq {J : Type u} [small_category J] {K : J ⥤ ProFiltPseuNormGrp₁.{u}}
  (C : limits.cone K) (hC : limits.is_limit C) (x y : C.X)
  (cond : ∀ j, C.π.app j x = C.π.app j y) : x = y :=
begin
  let D := limit_cone K,
  let hD : limits.is_limit D := limit_cone_is_limit _,
  let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso hD,
  apply_fun E.hom,
  swap, {
    intros a b h,
    apply_fun E.inv at h,
    change (E.hom ≫ E.inv) _ = (E.hom ≫ E.inv) _ at h,
    simpa using h },
  apply quotient.sound',
  refine ⟨_, le_sup_left, le_sup_right, _⟩,
  simp,
  ext j : 3,
  dsimp, simp,
  exact cond j,
end

lemma coe_comp_apply {A B C : ProFiltPseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
  (f ≫ g) x = g (f x) := rfl

def level : ℝ≥0 ⥤ ProFiltPseuNormGrp₁.{u} ⥤ Profinite.{u} :=
{ obj := λ c,
  { obj := λ M, Profinite.of $ pseudo_normed_group.filtration M c,
    map := λ A B f, ⟨_, f.level_continuous _⟩ },
  map := λ c₁ c₂ h,
  { app := λ M, by letI : fact (c₁ ≤ c₂) := ⟨h.le⟩;
      exact ⟨_, comphaus_filtered_pseudo_normed_group.continuous_cast_le _ _⟩ } } .

instance {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrp₁.{u}) (c : ℝ≥0) :
  limits.preserves_limit K (level.obj c) :=
begin
  constructor,
  intros E hE,
  apply limits.is_limit_of_reflects Profinite_to_CompHaus,
  change limits.is_limit ((CompHausFiltPseuNormGrp₁.level.obj c).map_cone
    (PFPNG₁_to_CHFPNG₁ₗₑ.map_cone E)),
  apply limits.is_limit_of_preserves,
  apply limits.is_limit_of_preserves,
  assumption
end

lemma mem_filtration_iff_of_is_limit {J : Type u} [small_category J]
  (K : J ⥤ ProFiltPseuNormGrp₁.{u}) (C : limits.cone K)
  (hC : limits.is_limit C) (c : ℝ≥0) (x : C.X) :
  x ∈ pseudo_normed_group.filtration C.X c ↔
  (∀ j : J, C.π.app j x ∈ pseudo_normed_group.filtration (K.obj j) c) :=
CompHausFiltPseuNormGrp₁.mem_filtration_iff_of_is_limit (K ⋙ PFPNG₁_to_CHFPNG₁ₗₑ)
  (PFPNG₁_to_CHFPNG₁ₗₑ.map_cone C) (limits.is_limit_of_preserves _ hC) _ _

lemma is_limit_ext {J : Type u} [small_category J]
  (K : J ⥤ ProFiltPseuNormGrp₁.{u}) (C : limits.cone K)
  (hC : limits.is_limit C) (x y : C.X)
  (h : ∀ j, C.π.app j x = C.π.app j y) : x = y :=
CompHausFiltPseuNormGrp₁.is_limit_ext _ _ (limits.is_limit_of_preserves PFPNG₁_to_CHFPNG₁ₗₑ hC) _ _ h

section explicit_product

def product {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrp₁.{u}) :
  ProFiltPseuNormGrp₁.{u} :=
{ M := Π i, X i,
  str := infer_instance,
  exhaustive' := (CompHausFiltPseuNormGrp₁.product (λ i, (PFPNG₁_to_CHFPNG₁ₗₑ.obj (X i)))).exhaustive' }

@[simps]
def product.π {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrp₁.{u}) (i) :
  product X ⟶ X i :=
CompHausFiltPseuNormGrp₁.product.π (λ i, (PFPNG₁_to_CHFPNG₁ₗₑ.obj (X i))) i

@[simps]
def product.lift {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrp₁.{u})
  (M : ProFiltPseuNormGrp₁.{u}) (f : Π i, M ⟶ X i) : M ⟶ product X :=
CompHausFiltPseuNormGrp₁.product.lift (λ i, (PFPNG₁_to_CHFPNG₁ₗₑ.obj (X i))) (PFPNG₁_to_CHFPNG₁ₗₑ.obj M) f

@[simp, reassoc]
lemma product.lift_π {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrp₁.{u})
  (M : ProFiltPseuNormGrp₁.{u}) (f : Π i, M ⟶ X i) (i) :
  product.lift X M f ≫ product.π X i = f i := by { ext, simp }

lemma product.lift_unique {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrp₁.{u})
  (M : ProFiltPseuNormGrp₁.{u}) (f : Π i, M ⟶ X i) (g : M ⟶ product X)
  (hg : ∀ i, g ≫ product.π X i = f i) : g = product.lift X M f :=
by { ext, simp [← hg] }

lemma product.hom_ext {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrp₁.{u})
  (M : ProFiltPseuNormGrp₁.{u}) (g₁ g₂ : M ⟶ product X)
  (h : ∀ i, g₁ ≫ product.π X i = g₂ ≫ product.π X i) : g₁ = g₂ :=
begin
  rw [product.lift_unique X M _ g₁ (λ i, rfl), product.lift_unique X M _ g₂ (λ i, rfl)],
  simp [h],
end

end explicit_product

end ProFiltPseuNormGrp₁
