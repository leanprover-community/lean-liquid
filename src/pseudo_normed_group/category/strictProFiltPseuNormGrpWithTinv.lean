import pseudo_normed_group.category.ProFiltPseuNormGrpWithTinv

universe variables u

open category_theory
open_locale nnreal

local attribute [instance] type_pow

noncomputable theory

/-- `ProFiltPseuNormGrpWithTinv₁ r` is the bundled category of
`profinitely_filtered_pseudo_normed_group_with_Tinv r`s, with
(this is the `₁`) exhaustive filtrations and strict morphisms.
The objects are filtered abelian groups equipped with an
endomorphism `T⁻¹` with norm at most `r`; see the docstring
of `profinitely_filtered_pseudo_normed_group_with_Tinv` for
more details.
-/
structure ProFiltPseuNormGrpWithTinv₁ (r : ℝ≥0) : Type (u+1) :=
(M : Type u)
[str : profinitely_filtered_pseudo_normed_group_with_Tinv r M]
(exhaustive' : ∀ m : M, ∃ c : ℝ≥0, m ∈ pseudo_normed_group.filtration M c)

namespace ProFiltPseuNormGrpWithTinv₁

variable (r : ℝ≥0)

instance : has_coe_to_sort (ProFiltPseuNormGrpWithTinv₁ r) Type* := ⟨λ M, M.M⟩
instance (M : ProFiltPseuNormGrpWithTinv₁ r) :
  profinitely_filtered_pseudo_normed_group_with_Tinv r M := M.str

lemma exhaustive (M : ProFiltPseuNormGrpWithTinv₁ r) (m : M) : ∃ c : ℝ≥0,
  m ∈ pseudo_normed_group.filtration M c := M.exhaustive' m

instance : large_category (ProFiltPseuNormGrpWithTinv₁.{u} r) :=
{ hom := λ A B, comphaus_filtered_pseudo_normed_group_with_Tinv_hom r A B,
  id := λ A, comphaus_filtered_pseudo_normed_group_with_Tinv_hom.id,
  comp := λ A B C f g, g.comp f } .

def enlarging_functor : (ProFiltPseuNormGrpWithTinv₁.{u} r) ⥤ (ProFiltPseuNormGrpWithTinv.{u} r) :=
{ obj := λ M, ProFiltPseuNormGrpWithTinv.of r M,
  map := λ A B f, f }

instance : concrete_category (ProFiltPseuNormGrpWithTinv₁.{u} r) :=
{ forget :=
  { obj := λ M, M,
    map := λ X Y f, f },
  forget_faithful := ⟨⟩ } .

-- PFPNGT₁_PFPNGT₁_to_PFPNG₁ₗₑₗₑ
/-- The "forget the action of T⁻¹" functor on profinitely filtered normed groups. -/
def _root_.PFPNGT₁_to_PFPNG₁ₗₑ : (ProFiltPseuNormGrpWithTinv₁.{u} r) ⥤ ProFiltPseuNormGrp₁.{u} :=
{ obj := λ M,
  { M := M,
    exhaustive' := M.exhaustive' },
  map := λ A B f,
  { to_fun := f,
    map_zero' := f.map_zero,
    map_add' := f.map_add,
    strict' := f.strict,
    continuous' := f.continuous' } }

/-- The functor which takes a profinitely filtered normed group with an action of T⁻¹,
then forgets the action and considered it as a `CompHaus`ly filtered normed group. -/
@[simps]
def PFPNGT₁_to_CHFPNG₁ₗₑ (r' : ℝ≥0) :
  ProFiltPseuNormGrpWithTinv₁.{u} r' ⥤ CompHausFiltPseuNormGrp₁.{u} :=
PFPNGT₁_to_PFPNG₁ₗₑ r' ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁

lemma coe_comp_apply {A B C : ProFiltPseuNormGrpWithTinv₁ r} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
  (f ≫ g) a = g (f a) := rfl

open profinitely_filtered_pseudo_normed_group_with_Tinv

def Tinv_limit_fun_aux {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r)
  (x : Σ (c : ℝ≥0), CompHausFiltPseuNormGrp₁.cone_point_type_filt
    ((K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r) ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) c) (j : J) :
  (pseudo_normed_group.filtration (K.obj j) x.fst) :=
x.2 j

def Tinv_limit_fun'
  {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r)
  (c : ℝ≥0) (x : CompHausFiltPseuNormGrp₁.cone_point_type_filt
    ((K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r) ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) c) :
  (Σ c, CompHausFiltPseuNormGrp₁.cone_point_type_filt
    ((K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r) ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) c) :=
⟨r⁻¹ * c, λ j,
  ⟨Tinv (Tinv_limit_fun_aux r K ⟨c,x⟩ j : K.obj j),
    (Tinv_mem_filtration _ _ (Tinv_limit_fun_aux r K ⟨c,x⟩ j).2)⟩,
  begin
    intros i j f,
    ext1,
    show (K.map f) (Tinv _) = Tinv _,
    erw (K.map f).map_Tinv, congr' 1,
    simpa only [functor.comp_map, subtype.val_eq_coe, subtype.ext_iff] using x.2 f,
  end⟩

def Tinv_limit_fun
  {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X) →
    ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X) :=
quotient.map' (λ x, Tinv_limit_fun' r K x.1 x.2)
begin
  rintros x y ⟨c, h₁, h₂, h⟩,
  refine ⟨r⁻¹ * c, mul_le_mul' le_rfl h₁, mul_le_mul' le_rfl h₂, _⟩,
  ext j,
  show Tinv (Tinv_limit_fun_aux r K x j : K.obj j) = Tinv (Tinv_limit_fun_aux r K y j : K.obj j),
  congr' 1,
  rw [subtype.ext_iff, function.funext_iff] at h,
  specialize h j, rwa [subtype.ext_iff] at h,
end

open CompHausFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁.cone_point_type

lemma Tinv_limit_fun_incl
  {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) (c : ℝ≥0) (x) :
  Tinv_limit_fun r K (incl c x) = incl (r⁻¹ * c) (Tinv_limit_fun' r K c x).2 := rfl

@[simps]
def Tinv_limit_add_monoid_hom
  {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X) →+
    ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X) :=
{ to_fun := Tinv_limit_fun r K,
  map_zero' :=
  begin
    apply quotient.sound',
    dsimp only,
    refine ⟨0, _, le_rfl, _⟩; dsimp only [Tinv_limit_fun'],
    { rw [mul_zero] },
    { ext j, exact Tinv.map_zero }
  end,
  map_add' :=
  begin
    rintros ⟨cx, x⟩ ⟨cy, y⟩,
    show Tinv_limit_fun r K (incl cx x + incl cy y) =
      Tinv_limit_fun r K (incl cx x) + Tinv_limit_fun r K (incl cy y),
    simp only [incl_add_incl, Tinv_limit_fun_incl],
    apply quotient.sound',
    dsimp only,
    refine ⟨_, le_rfl, _, _⟩; simp only [mul_add],
    ext j, refine Tinv.map_add _ _,
  end }

open pseudo_normed_group ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁

lemma Tinv_limit_aux {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r)
  (c : ℝ≥0) (x : ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X))
  (hx : x ∈ filtration (ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X c) :
  Tinv_limit_add_monoid_hom r K x ∈
    filtration (ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X (r⁻¹ * c) :=
begin
  obtain ⟨x,rfl⟩ := hx,
  dsimp only [Tinv_limit_add_monoid_hom_apply, Tinv_limit_fun_incl],
  exact ⟨_,rfl⟩,
end

-- TODO: break up this proof into pieces.
def Tinv_limit {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  comphaus_filtered_pseudo_normed_group_hom
    ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X)
    ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X) :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_bound (Tinv_limit_add_monoid_hom r K) r⁻¹
begin
  intro c,
  fsplit,
  { apply Tinv_limit_aux },
  { let X := ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X),
    let F : filtration X c → filtration X (r⁻¹ * c) := λ x,
      ⟨Tinv_limit_add_monoid_hom r K x, Tinv_limit_aux _ _ _ _ x.2⟩,
    change continuous F,
    let e := filt_homeo (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ _ ⋙ to_CHFPNG₁),
    suffices : continuous (e (r⁻¹ * c) ∘ F ∘ (e c).symm), by simpa,
    let I : Π (j : J), comphaus_filtered_pseudo_normed_group_hom (K.obj j) (K.obj j) :=
      λ j, Tinv,
    let G : cone_point_type_filt (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ _ ⋙ to_CHFPNG₁) c →
      cone_point_type_filt (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ _ ⋙ to_CHFPNG₁) (r⁻¹ * c) :=
      λ x, ⟨λ j, ⟨I j (x j).1, _⟩, _⟩,
    rotate,
    { apply Tinv_bound_by, exact (x j).2 },
    { intros i j e,
      have := x.2 e,
      ext,
      dsimp,
      apply_fun (λ e, e.val) at this,
      change _ = I j (x.val j).val,
      rw ← this,
      apply (K.map e).map_Tinv },
    have : continuous G,
    { apply continuous_subtype_mk,
      apply continuous_pi,
      intros i,
      let G1 : cone_point_type_filt (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ _ ⋙ to_CHFPNG₁) c →
        filtration (K.obj i) c := λ x, x i,
      let G2 : filtration (K.obj i) c → filtration (K.obj i) (r⁻¹ * c) :=
        λ x, ⟨I i x, _⟩,
      swap, { apply Tinv_bound_by, exact x.2 },
      change continuous (G2 ∘ G1),
      apply continuous.comp,
      { apply comphaus_filtered_pseudo_normed_group_hom.continuous, intros x, refl },
      { let G11 : cone_point_type_filt (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ _ ⋙ to_CHFPNG₁) c →
          Π j : J, filtration (K.obj j) c := λ x, x,
        let G12 : (Π j : J, filtration (K.obj j) c) → filtration (K.obj i) c := λ x, x i,
        change continuous (G12 ∘ G11),
        apply continuous.comp,
        apply continuous_apply,
        apply continuous_subtype_coe } },
    convert this,
    ext : 1,
    dsimp,
    apply_fun (e (r⁻¹ * c)).symm,
    simp,
    ext, refl },
end

instance {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  profinitely_filtered_pseudo_normed_group_with_Tinv r
    (ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X :=
{ Tinv := Tinv_limit r K,
  Tinv_mem_filtration := comphaus_filtered_pseudo_normed_group_hom.mk_of_bound_bound_by _ _ _,
  ..(infer_instance : profinitely_filtered_pseudo_normed_group _) }

def limit_cone {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  limits.cone K :=
{ X :=
  { M := (ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X,
    exhaustive' := (ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).X.exhaustive },
  π :=
  { app := λ j,
    { map_Tinv' := begin
        rintro ⟨⟨c,x⟩⟩,
        dsimp [Tinv, Tinv_limit, Tinv_limit_fun, Tinv_limit_fun', Tinv_limit_fun_aux],
        dsimp [ProFiltPseuNormGrp₁.limit_cone, CompHausFiltPseuNormGrp₁.limit_cone],
        change proj (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r ⋙ to_CHFPNG₁) j (incl _ _) = _,
        change _ = Tinv (proj _ _ (incl _ _)),
        dsimp [proj],
        simpa,
      end,
      ..(ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).π.app j },
  naturality' := begin
    intros i j e,
    ext1 x,
    have := (ProFiltPseuNormGrp₁.limit_cone (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).π.naturality e,
    apply_fun (λ e, e x) at this,
    exact this,
  end } } .

instance {J : Type u} [small_category J] : creates_limits_of_shape J (PFPNGT₁_to_PFPNG₁ₗₑ r) :=
{ creates_limit := λ K,
  { reflects := λ C hC,
    { lift := λ S,
      { map_Tinv' := begin
          intros x,
          apply ProFiltPseuNormGrp₁.eq_of_π_eq _ hC,
          intros j,
          erw [← ProFiltPseuNormGrp₁.coe_comp_apply, ← ProFiltPseuNormGrp₁.coe_comp_apply,
            hC.fac],
          dsimp,
          change S.π.app _ _ = C.π.app _ _,
          rw [(S.π.app _).map_Tinv, (C.π.app _).map_Tinv],
          congr' 1,
          change _ = ((PFPNGT₁_to_PFPNG₁ₗₑ r).map (C.π.app j)) _,
          erw [← ProFiltPseuNormGrp₁.coe_comp_apply, hC.fac],
          refl,
        end,
        ..hC.lift ((PFPNGT₁_to_PFPNG₁ₗₑ r).map_cone S) },
      fac' := begin
        intros S j,
        ext1 x,
        have := hC.fac ((PFPNGT₁_to_PFPNG₁ₗₑ r).map_cone S) j,
        apply_fun (λ e, e x) at this,
        exact this,
      end,
      uniq' := begin
        intros S m h,
        ext1 x,
        have := hC.uniq ((PFPNGT₁_to_PFPNG₁ₗₑ r).map_cone S) ((PFPNGT₁_to_PFPNG₁ₗₑ r).map m) _,
        apply_fun (λ e, e x) at this,
        exact this,
        { intros j,
          ext y,
          specialize h j,
          apply_fun (λ e, e y) at h,
          exact h },
      end },
    lifts := λ C hC,
    { lifted_cone := limit_cone r K,
      valid_lift :=
        (ProFiltPseuNormGrp₁.limit_cone_is_limit (K ⋙ PFPNGT₁_to_PFPNG₁ₗₑ r)).unique_up_to_iso hC } } }

instance : creates_limits (PFPNGT₁_to_PFPNG₁ₗₑ r) := ⟨⟩

instance (r') : creates_limits (PFPNGT₁_to_CHFPNG₁ₗₑ r') :=
category_theory.comp_creates_limits _ _

def limit_cone_is_limit {J : Type u} [small_category J]
  (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) : limits.is_limit (limit_cone r K) :=
limits.is_limit_of_reflects (PFPNGT₁_to_PFPNG₁ₗₑ r) (ProFiltPseuNormGrp₁.limit_cone_is_limit _)

instance : limits.has_limits (ProFiltPseuNormGrpWithTinv₁.{u} r) :=
has_limits_of_has_limits_creates_limits (PFPNGT₁_to_PFPNG₁ₗₑ r)

lemma is_limit_ext {J : Type u} [small_category J]
  (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) (C : limits.cone K)
  (hC : limits.is_limit C) (x y : C.X)
  (h : ∀ j, C.π.app j x = C.π.app j y) : x = y :=
ProFiltPseuNormGrp₁.is_limit_ext _ _ (limits.is_limit_of_preserves (PFPNGT₁_to_PFPNG₁ₗₑ r) hC) _ _ h

section explicit_products

def product {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r) :
  ProFiltPseuNormGrpWithTinv₁.{u} r :=
{ M := Π i, X i,
  -- Why couldn't typeclass inference find this?
  str := profinitely_filtered_pseudo_normed_group_with_Tinv.pi _ _,
  exhaustive' := (ProFiltPseuNormGrp₁.product (λ i, ((PFPNGT₁_to_PFPNG₁ₗₑ r).obj (X i)))).exhaustive' } .

@[simps]
def product.π {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r) (i) :
  product r X ⟶ X i :=
{ map_Tinv' := λ x, rfl,
  ..(ProFiltPseuNormGrp₁.product.π (λ i, (PFPNGT₁_to_PFPNG₁ₗₑ r).obj (X i))) i }

@[simps]
def product.lift {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r)
  (M : ProFiltPseuNormGrpWithTinv₁.{u} r) (f : Π i, M ⟶ X i) : M ⟶ product r X :=
{ map_Tinv' := begin
    intros x,
    ext i,
    change ⇑(product.lift (λ (i : α), (PFPNGT₁_to_PFPNG₁ₗₑ r).obj (X i)) ((PFPNGT₁_to_PFPNG₁ₗₑ r).obj M)
      (λ (i : α), (PFPNGT₁_to_PFPNG₁ₗₑ r).map (f i))) (Tinv x) i = _,
    rw ProFiltPseuNormGrp₁.product.lift_to_fun,
    erw (f i).map_Tinv,
    refl,
  end,
  ..(ProFiltPseuNormGrp₁.product.lift
      (λ i, (PFPNGT₁_to_PFPNG₁ₗₑ r).obj (X i))
      ((PFPNGT₁_to_PFPNG₁ₗₑ r).obj M)
      (λ i, (PFPNGT₁_to_PFPNG₁ₗₑ r).map (f i))) }

@[simp, reassoc]
lemma product.lift_π {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r)
  (M : ProFiltPseuNormGrpWithTinv₁.{u} r) (f : Π i, M ⟶ X i) (i) :
  product.lift r X M f ≫ product.π r X i = f i := by { ext, simpa }

lemma product.lift_unique {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r)
  (M : ProFiltPseuNormGrpWithTinv₁.{u} r) (f : Π i, M ⟶ X i) (g : M ⟶ product r X)
  (hg : ∀ i, g ≫ product.π r X i = f i) : g = product.lift r X M f :=
by { ext, simpa [← hg] }

lemma product.hom_ext {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r)
  (M : ProFiltPseuNormGrpWithTinv₁.{u} r) (g₁ g₂ : M ⟶ product r X)
  (h : ∀ i, g₁ ≫ product.π r X i = g₂ ≫ product.π r X i) : g₁ = g₂ :=
begin
  rw [product.lift_unique r X M _ g₁ (λ i, rfl), product.lift_unique r X M _ g₂ (λ i, rfl)],
  simp [h],
end

def product.fan {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r) :
  limits.fan X := limits.fan.mk (product r X) $ λ b, product.π _ _ _

def product.is_limit {α : Type u} [fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r) :
  limits.is_limit (product.fan r X) :=
{ lift := λ M, product.lift _ _ _ $ λ i, M.π.app i,
  fac' := begin
    intros S j,
    dsimp [product.fan],
    simp,
  end,
  uniq' := begin
    intros S m hm,
    apply product.hom_ext,
    intros i,
    dsimp [product.fan] at hm,
    simp [hm],
  end }

end explicit_products

end ProFiltPseuNormGrpWithTinv₁
