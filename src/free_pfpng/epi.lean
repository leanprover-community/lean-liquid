import free_pfpng.setup
import data.sign

noncomputable theory

open_locale classical big_operators

open category_theory
open opposite

universe u

instance Condensed_Ab_to_CondensedSet_faithful :
  faithful Condensed_Ab_to_CondensedSet :=
{ map_injective' := begin
    intros X Y f g h, ext W t : 4,
    apply_fun (λ e, e.val.app W t) at h, dsimp at h,
    exact h
  end }

lemma category_theory.epi_to_colimit_of_exists {J : Type u}
  [small_category J] {C : Type*} [category.{u} C]
  {F : J ⥤ C} (T : C)
  (E : limits.cocone F) (hE : limits.is_colimit E)
  (f : T ⟶ E.X)
  (h : ∀ j : J,
    ∃ (Z : C) (p : Z ⟶ T) (q : Z ⟶ F.obj j) (hq : epi q),
      q ≫ E.ι.app j = p ≫ f) : epi f :=
begin
  constructor, intros W a b hh,
  apply hE.hom_ext, intros j, specialize h j,
  obtain ⟨Z,p,q,hq,w⟩ := h, resetI,
  rw ← cancel_epi q, simp_rw [← category.assoc, w,
    category.assoc, hh],
end

lemma epi_Profinite_to_Condensed_map_of_epi {X Y : Profinite.{u}}
  (f : X ⟶ Y) [hf : epi f] : epi (Profinite_to_Condensed.map f) :=
begin
  constructor, intros Z a b h, ext W q : 34, induction W using opposite.rec,
  have hZ := Z.2,
  rw is_sheaf_iff_is_sheaf_of_type at hZ,
  rw Z.val.is_proetale_sheaf_of_types_tfae.out 0 1 at hZ,
  let q' := q.down,
  dsimp at q q',
  dsimp [functor.is_proetale_sheaf_of_types] at hZ,
  specialize hZ punit W (λ _, Profinite.pullback f q')
    (λ _, Profinite.pullback.snd _ _) _ _,
  { intro w,
    rw Profinite.epi_iff_surjective at hf,
    obtain ⟨x, hx⟩ := hf (q' w),
    refine ⟨punit.star, ⟨(x, w), hx⟩, rfl⟩, },
  { intros i, dsimp, refine Z.val.map _ (b.val.app (op W) q),
    refine quiver.hom.op _, exact Profinite.pullback.snd _ _ },
  specialize hZ _,
  { clear hZ,
    rintro ⟨⟩ ⟨⟩ S g₁ g₂ H, dsimp only at H,
    apply_fun (λ φ, Z.val.map φ.op (b.val.app (op W) q)) at H,
    simp only [op_comp, Z.val.map_comp] at H, exact H, },
  obtain ⟨t,ht1,ht2⟩ := hZ,
  have : b.val.app (op W) q = t,
  { apply ht2,
    intros i, refl },
  rw this, apply ht2,
  intros i, dsimp,
  change (a.val.app (op W) ≫ Z.val.map _) q =
    (b.val.app (op W) ≫ Z.val.map _) q,
  simp only [← nat_trans.naturality],
  dsimp,
  apply_fun (λ e, Profinite_to_Condensed.map (Profinite.pullback.fst f q') ≫ e) at h,
  apply_fun (λ e, e.val.app (op (Profinite.pullback f q'))) at h,
  dsimp at h,
  let i : (Profinite.pullback f q').to_Condensed.val.obj (op (Profinite.pullback f q')) :=
    ulift.up (𝟙 _),
  apply_fun (λ e, e i) at h,
  dsimp [ulift_functor] at h,
  convert h,
  all_goals
  { ext1,
    dsimp [Profinite.to_Condensed],
    simp only [category.id_comp, Profinite.pullback.condition] },
end

/-
inductive pmz : set ℤ
| neg_one : pmz (-1)
| zero : pmz 0
| one : pmz 1

def pmz_eq : pmz = {0,1,-1} :=
begin
  ext, split,
  { intros h, cases h, right, right, simpa, left, simp, right, left, simp },
  { intros h, simp at h, rcases h with (rfl|rfl|rfl),
    apply pmz.zero,
    apply pmz.one,
    apply pmz.neg_one }
end

lemma pmz_finite : set.finite pmz :=
by simp [pmz_eq]

instance fintype_pmz : fintype pmz := pmz_finite.fintype
-/

--abbreviation Profinite.pow (S : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
--Profinite.product (λ i : fin n, S)

/-- `S.pmz n` is `(S × {-1,0,1})^n`. -/
def Profinite.pmz (S : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
Profinite.sigma $ λ (x : ulift.{u} (fin n → sign_type)), S.pow n

/-- the canonical map of condensed sets `(S × {-1,0,1})^n ⟶ ℤ[S]` -/
def Profinite.pmz_to_free' (S : Profinite.{u}) (n : ℕ) :
  (S.pmz n).to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj S.free' :=
(Profinite.to_Condensed_equiv (S.pmz n) (Condensed_Ab_to_CondensedSet.obj S.free')).symm $
  (CondensedSet.val_obj_sigma_equiv (λ (f : ulift.{u} (fin n → sign_type)), S.pow n)
    (Condensed_Ab_to_CondensedSet.obj S.free')).symm $
λ (f : ulift.{u} (fin n → sign_type)),
let e := proetale_topology.to_sheafify (S.to_Condensed.val ⋙ AddCommGroup.free') in
e.app (op $ S.pow n) $
  ∑ i : fin n, finsupp.single (ulift.up $ Profinite.product.π _ i) (f.down i : ℤ)

def Profinite.pmz_functor (n : ℕ) : Profinite.{u} ⥤ Profinite.{u} :=
{ obj := λ S, S.pmz n,
  map := λ S T f,
    Profinite.sigma.desc _ $ λ e,
      (Profinite.product.lift (λ i : fin n, T)
        (λ i, Profinite.product.π _ i ≫ f)) ≫ Profinite.sigma.ι _ e,
  map_id' := begin
    intros X,
    apply Profinite.sigma.hom_ext, intros e,
    erw category.comp_id, refl,
  end,
  map_comp' := begin
    intros X Y Z f g,
    apply Profinite.sigma.hom_ext, intros e, dsimp, simp,
    erw [Profinite.sigma.ι_desc],
    refl,
  end }

def Profinite.pmz_diagram (S : Profinite.{u}) (n : ℕ) :
  discrete_quotient S ⥤ Profinite.{u} :=
S.diagram ⋙ Profinite.pmz_functor n

def Profinite.pmz_cone (S : Profinite.{u}) (n : ℕ) : limits.cone (S.pmz_diagram n) :=
(Profinite.pmz_functor n).map_cone S.as_limit_cone

def Profinite.sigma_functor {J : Type u} [small_category J]
  (F : J ⥤ Profinite.{u}) (α : Type u) [fintype α] :
  J ⥤ Profinite.{u} :=
{ obj := λ j, Profinite.sigma (λ a : α, F.obj j),
  map := λ i j e, Profinite.sigma.desc _ $ λ a,
    F.map e ≫ Profinite.sigma.ι _ a,
  map_id' := begin
    intros j, apply Profinite.sigma.hom_ext, intros a,
    simp,
  end,
  map_comp' := begin
    intros i j k e f,
    apply Profinite.sigma.hom_ext, intros a,
    simp,
  end }

def Profinite.sigma_cone {J : Type u} [small_category J]
  {F : J ⥤ Profinite.{u}} (α : Type u) [fintype α]
  (E : limits.cone F) :
  limits.cone (Profinite.sigma_functor F α) :=
{ X := Profinite.sigma (λ a : α, E.X),
  π :=
  { app := λ j, Profinite.sigma.desc _ $ λ a,
      E.π.app j ≫ Profinite.sigma.ι _ a,
    naturality' := begin
      intros i j e, dsimp,
      apply Profinite.sigma.hom_ext, intros a,
      simp, dsimp [Profinite.sigma_functor], simp,
    end } }

def Profinite.sigma_to_limit {J : Type u} [small_category J]
  (F : J ⥤ Profinite.{u}) (α : Type u) [fintype α]
  (E : limits.cone F) :
  (Profinite.sigma_cone α E).X ⟶
    (Profinite.limit_cone (Profinite.sigma_functor F α)).X :=
Profinite.sigma.desc _ $ λ a, (Profinite.limit_cone_is_limit
  (Profinite.sigma_functor F α)).lift ⟨E.X,
  { app := λ j, E.π.app j ≫ Profinite.sigma.ι _ a,
  naturality' := begin
    intros i j e, dsimp [Profinite.sigma_functor],
    simp,
  end }⟩

lemma Profinite.exists_of_sigma_limit {J : Type u} [small_category J]
  (F : J ⥤ Profinite.{u}) (α : Type u) [fintype α] [is_cofiltered J]
  (t : (Profinite.limit_cone (Profinite.sigma_functor F α)).X) :
  ∃ (a₀ : α) (t₀ : (Profinite.limit_cone F).X),
    ∀ j : J, Profinite.sigma.ι _ a₀
      ((Profinite.limit_cone F).π.app j t₀) =
      (Profinite.limit_cone (Profinite.sigma_functor F α)).π.app j t :=
begin
  rcases t with ⟨t,ht⟩, dsimp at ht,
  obtain ⟨j₀⟩ : nonempty J := is_cofiltered.nonempty,
  let a₀ := (t j₀).1, use a₀,
  have h1 : ∀ ⦃i j : J⦄ (f : i ⟶ j), (t i).1 = (t j).1,
  { intros i j e, specialize ht e,
    apply_fun (λ q, q.1) at ht,
    cases t i, exact ht },
  have h2 : ∀ j : J, (t j).1 = a₀,
  { intros j,
    let j₁ := is_cofiltered.min j j₀,
    rw ← h1 (is_cofiltered.min_to_left j j₀), dsimp [a₀],
    rw ← h1 (is_cofiltered.min_to_right j j₀) },
  let t₀ : (Profinite.limit_cone F).X := ⟨_,_⟩,
  rotate,
  { intros j, exact (t j).2 },
  { intros i j e,
    specialize ht e,
    cases (t i),
    dsimp [Profinite.sigma_functor, Profinite.sigma.desc, Profinite.sigma.ι] at ht,
    cases t j,
    erw sigma.mk.inj_iff at ht,
    exact eq_of_heq ht.2 },
  use t₀,
  intros j,
  dsimp [Profinite.limit_cone, Profinite.sigma_functor, Profinite.sigma.ι,
    Profinite.sigma.desc, CompHaus.limit_cone, Top.limit_cone], ext,
  exact (h2 _).symm, refl,
end

lemma Profinite.bijective_sigma_to_limit {J : Type u} [small_category J]
  (F : J ⥤ Profinite.{u}) (α : Type u) [fintype α]
  (E : limits.cone F) (hE : limits.is_limit E) [is_cofiltered J] :
  function.bijective (Profinite.sigma_to_limit F α E) :=
begin
  split,
  { rintros ⟨a,x⟩ ⟨b,y⟩ h,
    dsimp [Profinite.sigma_to_limit, Profinite.sigma.desc,
      Profinite.limit_cone_is_limit, CompHaus.limit_cone_is_limit,
      Top.limit_cone_is_limit] at h,
    apply_fun (λ e, e.1) at h,
    have hh := h,
    obtain ⟨j₀⟩ : nonempty J := is_cofiltered.nonempty,
    apply_fun (λ e, (e j₀).1) at h, dsimp [Profinite.sigma.ι] at h,
    subst h, ext, refl,
    apply heq_of_eq,
    apply limits.concrete.is_limit_ext _ hE,
    intros jj, apply_fun (λ e, e jj) at hh,
    erw sigma.mk.inj_iff at hh,
    exact eq_of_heq hh.2 },
  { rintros t,
    obtain ⟨a,s,ht⟩ := Profinite.exists_of_sigma_limit F α t,
    use a, let EE : E.X ≅ (Profinite.limit_cone F).X :=
      hE.cone_point_unique_up_to_iso (Profinite.limit_cone_is_limit _),
    use EE.inv s, dsimp, ext j : 2,
    convert ht j, ext, refl,
    apply heq_of_eq,
    change ((hE.lift (Profinite.limit_cone F)) ≫ E.π.app j) s = _,
    rw hE.fac, refl }
end

lemma Profinite.is_iso_lift_sigma_cone {J : Type u} [small_category J]
  {F : J ⥤ Profinite.{u}} (α : Type u) [fintype α] [is_cofiltered J]
  (E : limits.cone F) (hE : limits.is_limit E) :
  is_iso ((Profinite.limit_cone_is_limit _).lift (Profinite.sigma_cone α E)) :=
begin
  apply Profinite.is_iso_of_bijective,
  convert Profinite.bijective_sigma_to_limit F α E hE,
  symmetry,
  apply (Profinite.limit_cone_is_limit (Profinite.sigma_functor F α)).uniq,
  intros j,
  apply Profinite.sigma.hom_ext,
  intros a, refl,
end

def Profinite.sigma_cone_is_limit {J : Type u} [small_category J]
  {F : J ⥤ Profinite.{u}} (α : Type u) [fintype α] [is_cofiltered J]
  (E : limits.cone F) (hE : limits.is_limit E) :
  limits.is_limit (Profinite.sigma_cone α E) :=
begin
  haveI : is_iso ((Profinite.limit_cone_is_limit _).lift (Profinite.sigma_cone α E)) :=
    Profinite.is_iso_lift_sigma_cone α E hE,
  apply limits.is_limit.of_point_iso (Profinite.limit_cone_is_limit _),
  assumption
end

def Profinite.pmz_to_limit (S : Profinite.{u}) (n : ℕ) :
  S.pmz n ⟶ (Profinite.limit_cone (S.pmz_diagram n)).X :=
Profinite.sigma.desc _ $ λ f,
  (Profinite.limit_cone_is_limit (S.pmz_diagram n)).lift ⟨S.pow n,
  { app := λ T, Profinite.map_pow (S.as_limit_cone.π.app T) n ≫
      Profinite.sigma.ι _ f,
    naturality' := begin
      intros A B e,
      dsimp [Profinite.pmz_diagram, Profinite.pmz_functor],
      simpa,
    end }⟩

def Profinite.pow_functor (n : ℕ) : Profinite.{u} ⥤ Profinite.{u} :=
{ obj := λ S, S.pow n,
  map := λ S T f, Profinite.map_pow f n,
  map_id' := begin
    intros X, apply Profinite.product.hom_ext, intros i, dsimp [Profinite.map_pow], simp,
  end,
  map_comp' := begin
    intros X Y Z f g,
    apply Profinite.product.hom_ext, intros i, dsimp [Profinite.map_pow], simp,
  end }

def Profinite.pow_cone {J : Type u} [small_category J] {F : J ⥤ Profinite.{u}}
  (E : limits.cone F) (n : ℕ) : limits.cone (F ⋙ Profinite.pow_functor n) :=
(Profinite.pow_functor n).map_cone E

def Profinite.pow_cone_is_limit
  {J : Type u} [small_category J] {F : J ⥤ Profinite.{u}}
  (E : limits.cone F) (hE : limits.is_limit E) (n : ℕ) :
  limits.is_limit (Profinite.pow_cone E n) :=
{ lift := λ Q, Profinite.product.lift _ $ λ a,
    hE.lift ⟨Q.X,
    { app := λ j, Q.π.app j ≫ Profinite.product.π _ a,
      naturality' := begin
        intros i j e, dsimp,
        simp only [category.id_comp, category.assoc],
        rw ← Q.w e,
        dsimp [Profinite.pow_functor, Profinite.map_pow],
        simp,
      end }⟩,
  fac' := begin
    intros Q j, apply Profinite.product.hom_ext, intros i,
    dsimp [Profinite.pow_cone, Profinite.pow_functor, Profinite.map_pow],
    simp only [category.assoc, Profinite.product.lift_π, Profinite.product.lift_π_assoc,
      limits.is_limit.fac],
  end,
  uniq' := begin
    intros Q m hm,
    apply Profinite.product.hom_ext, intros a,
    dsimp [Profinite.pow_cone, Profinite.pow_functor, Profinite.map_pow],
    simp only [Profinite.product.lift_π],
    apply hE.hom_ext,
    intros j,
    simp only [category.assoc, limits.is_limit.fac], rw ← hm,
    dsimp [Profinite.pow_cone, Profinite.pow_functor, Profinite.map_pow],
    simp only [category.assoc, Profinite.product.lift_π],
  end }

lemma Profinite.is_iso_pmz_to_limit (S : Profinite.{u}) (n : ℕ) :
  is_iso (S.pmz_to_limit n) :=
begin
  let E := Profinite.sigma_cone (ulift.{u} (fin n → sign_type))
    (Profinite.pow_cone S.as_limit_cone n),
  let hE : limits.is_limit E := Profinite.sigma_cone_is_limit _ _
    (Profinite.pow_cone_is_limit _ S.as_limit n),
  let q : E.X ≅ (Profinite.limit_cone (S.pmz_diagram n)).X :=
    hE.cone_point_unique_up_to_iso (Profinite.limit_cone_is_limit _),
  have : is_iso q.hom := infer_instance,
  convert this,
  apply Profinite.sigma.hom_ext, intros e,
  apply (Profinite.limit_cone_is_limit _).hom_ext,
  intros T,
  refl,
end

def Profinite.pmz_cone_is_limit (S : Profinite.{u}) (n : ℕ) :
  limits.is_limit (S.pmz_cone n) :=
begin
  apply limits.is_limit.of_point_iso (Profinite.limit_cone_is_limit _),
  convert Profinite.is_iso_pmz_to_limit S n,
  apply Profinite.sigma.hom_ext, intros a,
  apply (Profinite.limit_cone_is_limit _).hom_ext, intros j,
  refl,
end

-- A finite product of finite discrete sets is discrete.
instance Profinite.discrete_topology_pow
  (S : Profinite.{u}) [discrete_topology S] (n : ℕ) :
  discrete_topology (S.pow n) :=
Pi.discrete_topology

-- A finite union of finite products of finite discrete sets is discrete.
instance Profinite.discrete_topology_pmz
  (S : Profinite.{u}) [discrete_topology S] (n : ℕ) :
  discrete_topology (S.pmz n) :=
sigma.discrete_topology

-- move this
lemma _root_.sign_type.nnnorm_coe_int_le_one : ∀ i : sign_type, ∥(i : ℤ)∥₊ ≤ 1
| sign_type.zero := by { erw [nnnorm_zero], exact zero_le', }
| sign_type.neg := by { erw [nnnorm_neg], norm_num, }
| sign_type.pos := by { erw [nnnorm_one], }

def Profinite.pmz_to_level_component (S : Profinite.{u}) (j : nnreal) (T : discrete_quotient S)
  (e : fin ⌊j⌋₊ → sign_type) :
  (Profinite.of ↥T).pow ⌊j⌋₊ ⟶
  (ProFiltPseuNormGrp₁.level.obj j).obj (free_pfpng_functor.obj (Fintype.of ↥T)) :=
{ to_fun := λ t,
  { val := ∑ i : fin ⌊j⌋₊, (λ s, if t i = s then (e i : ℤ) else 0),
    property := begin
      have : ∑ i : fin ⌊j⌋₊, (∑ s : T, if t i = s then (1 : nnreal) else 0) ≤ j,
      { calc _
            ≤ ∑ i : fin ⌊j⌋₊, (1 : nnreal) : _
        ... ≤ j : _,
        { apply finset.sum_le_sum, rintro i -, apply le_of_eq,
          erw [finset.sum_eq_single_of_mem (t i : T) (@finset.mem_univ T _ _), if_pos rfl],
          rintro s - hs, rw [if_neg hs.symm], },
        { simp only [finset.sum_const, finset.card_fin, nat.smul_one_eq_coe],
          exact nat.floor_le zero_le' } },
      apply pseudo_normed_group.filtration_mono this,
      apply pseudo_normed_group.sum_mem_filtration,
      rintro i -,
      apply finset.sum_le_sum,
      rintro s -,
      dsimp,
      split_ifs,
      { apply sign_type.nnnorm_coe_int_le_one },
      { rw nnnorm_zero },
    end },
  continuous_to_fun := continuous_of_discrete_topology }

def Profinite.pmz_to_level (S : Profinite.{u}) (j : nnreal) (T : discrete_quotient S) :
  (Profinite.of T).pmz ⌊j⌋₊ ⟶
    (ProFiltPseuNormGrp₁.level.obj j).obj (free_pfpng_functor.obj $ Fintype.of T) :=
Profinite.sigma.desc _ $ λ e, S.pmz_to_level_component j T (ulift.down e)

lemma Profinite.pmz_to_level_nat_trans_aux
  (S : Profinite.{u}) (j : nnreal) (T₁ T₂ : discrete_quotient S) (f : T₁ ⟶ T₂)
  (e : fin ⌊j⌋₊ → sign_type) (t : (Profinite.of T₁).pow ⌊j⌋₊) (s : T₂) :
(∑ i : fin ⌊j⌋₊, λ s : T₂, ite (S.fintype_diagram.map f (t i) = s) (e i : ℤ) 0) s =
  (@finset.filter (@bundled.α fintype (S.fintype_diagram.obj T₁))
     (λ w : T₁, S.fintype_diagram.map f w = s)
     (λ (a : @bundled.α fintype (S.fintype_diagram.obj T₁)),
        classical.prop_decidable _)
     (@finset.univ (@bundled.α fintype (S.fintype_diagram.obj T₁))
        (@Fintype.fintype (S.fintype_diagram.obj T₁)))).sum
    (∑ (i : fin ⌊j⌋₊), λ s : T₁, @ite ℤ (t i = s) _ ↑(e i) 0) :=
begin
  simp only [finset.sum_apply],
  rw finset.sum_comm,
  refine finset.sum_congr rfl _,
  rintro i -,
  rw finset.sum_ite_eq,
  simp only [finset.mem_filter, finset.mem_univ, true_and],
end

def Profinite.pmz_to_level_nat_trans (S : Profinite.{u}) (j : nnreal) :
  S.pmz_diagram ⌊j⌋₊ ⟶ (S.fintype_diagram ⋙ free_pfpng_functor) ⋙
    (ProFiltPseuNormGrp₁.level.obj j) :=
{ app := λ T, S.pmz_to_level j T,
  naturality' := begin
    intros T₁ T₂ f,
    dsimp [Profinite.pmz_diagram, Profinite.pmz_to_level, Profinite.pmz_functor],
    apply Profinite.sigma.hom_ext,
    rintro ⟨e⟩,
    simp only [Profinite.sigma.ι_desc_assoc, category.assoc, Profinite.sigma.ι_desc],
    ext t s,
    exact Profinite.pmz_to_level_nat_trans_aux S j T₁ T₂ f e t s,
  end }

def Profinite.pmz_to_free_pfpng (S : Profinite.{u}) (j : nnreal) :
  S.pmz ⌊j⌋₊ ⟶ (ProFiltPseuNormGrp₁.level.obj j).obj S.free_pfpng :=
let E := limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj j)
  (limits.limit.is_limit (S.fintype_diagram ⋙ free_pfpng_functor)) in
E.map (S.pmz_cone _) (S.pmz_to_level_nat_trans j)

lemma Profinite.is_limit.surjective_of_surjective
  {J : Type u} [small_category J] (F G : J ⥤ Profinite.{u})
  (α : F ⟶ G) (cF : limits.cone F)
  (cG : limits.cone G) (hcF : limits.is_limit cF) (hcG : limits.is_limit cG)
  [is_cofiltered J] (surj : ∀ (j : J), function.surjective ⇑(α.app j)) :
  function.surjective ⇑(limits.is_limit.map cF hcG α) :=
begin
  have := CompHaus.is_limit.surjective_of_surjective
    (F ⋙ Profinite_to_CompHaus)
    (G ⋙ Profinite_to_CompHaus)
    (whisker_right α _)
    (Profinite_to_CompHaus.map_cone cF)
    (Profinite_to_CompHaus.map_cone cG)
    (limits.is_limit_of_preserves _ hcF)
    (limits.is_limit_of_preserves _ hcG)
    surj,
  change function.surjective
    (Profinite_to_CompHaus.map (limits.is_limit.map cF hcG α)),
  convert this,
  apply hcG.hom_ext, intros j,
  simp only [limits.is_limit.map_π, iso.trans_hom, iso.symm_hom,
    functor.map_iso_hom, limits.is_limit.unique_up_to_iso_hom,
    limits.cone.category_comp_hom, limits.is_limit.lift_cone_morphism_hom,
    limits.limit.is_limit_lift, limits.cones.functoriality_map_hom,
    Profinite_to_CompHaus_map],
  erw [category.assoc, category.assoc],
  erw hcG.fac,
  have := (lifted_limit_maps_to_original
    (limits.limit.is_limit (G ⋙ Profinite_to_CompHaus))).inv.w j,
  erw this,
  dsimp, simp only [limits.limit.lift_π, limits.cones.postcompose_obj_π,
    nat_trans.comp_app, functor.map_cone_π_app,
    Profinite_to_CompHaus_map, whisker_right_app],
  refl,
end

lemma Profinite.pmz_to_free_pfpng_epi_aux {T : Type*} [fintype T]
  (r : nnreal)
  (f : T → ℤ)
  (hf : ∑ i : T, ∥ f i ∥₊ ≤ r) :
  ∃ (e : fin ⌊r⌋₊ → sign_type) (t : fin ⌊r⌋₊ → T),
  (∑ (i : fin ⌊r⌋₊), (λ (s : T), if (t i = s) then (e i : ℤ) else 0)) = f :=
sorry

instance Profinite.pmz_to_free_pfpng_epi (S : Profinite.{u}) (j : nnreal) :
  epi (S.pmz_to_free_pfpng j) :=
begin
  rw Profinite.epi_iff_surjective,
  dsimp only [Profinite.pmz_to_free_pfpng],
  have := Profinite.is_limit.surjective_of_surjective _ _ (S.pmz_to_level_nat_trans j)
    (S.pmz_cone _)
    ((ProFiltPseuNormGrp₁.level.obj j).map_cone (limits.limit.cone _))
    (S.pmz_cone_is_limit _)
    (limits.is_limit_of_preserves _ (limits.limit.is_limit _)),
  apply this,
  intros T,
  rintros ⟨(f : T → ℤ), hf : ∑ i : T, _ ≤ _⟩,
  obtain ⟨e,t,ht⟩ := Profinite.pmz_to_free_pfpng_epi_aux j f hf,
  change ∃ a : Σ i, fin ⌊j⌋₊ → T, _,
  use ulift.up e, use t, apply subtype.ext,
  dsimp [Profinite.pmz_to_level_nat_trans, Profinite.pmz_to_level,
    Profinite.sigma.desc, Profinite.pmz_to_level_component],
  convert ht,
  ext p,
  split_ifs; refl,
end

.

/-
#check free'_lift
lemma Profinite.free'_lift_eq (S : Profinite.{u}) (A : Condensed.{u} Ab.{u+1})
  (η : S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj A)
  (T : Profinite.{u}) :
  (S.free'_lift η).val.app (op T) =
  sorry := sorry
-/

namespace Profinite.epi_free'_to_condensed_setup

variables (S : Profinite.{u}) (j : nnreal)

#check S.free'_lift

lemma free'_lift_app_eq (A : Condensed.{u} Ab.{u+1})
  (η : S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj A)
  (T : Profinite.{u}) :
  (proetale_topology.to_sheafify _).app _ ≫ (S.free'_lift η).val.app (op T) =
  free'_lift (η.val.app _) :=
begin
  dsimp [Profinite.free'_lift],
  rw [← nat_trans.comp_app, proetale_topology.to_sheafify_sheafify_lift],
  dsimp [adjunction.whisker_right, free'_lift], simp,
end

lemma free'_lift_app_eq' (A : Condensed.{u} Ab.{u+1})
  (η : S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj A)
  (T : Profinite.{u}) :
  (proetale_topology.to_sheafify _).app _ ≫ (S.free'_lift η).val.app (op T) =
  ((finsupp.lift ↥(A.val.obj (op T)) ℤ
      (((Sheaf_to_presheaf proetale_topology (Type (u+1))).obj S.to_Condensed).obj (op T)))
   (η.val.app (op T))).to_add_monoid_hom :=
begin
  rw free'_lift_app_eq, rw free'_lift_eq_finsupp_lift,
end

instance (A : Condensed.{u} Ab.{u+1}) (T) :
  add_comm_group ((Condensed_Ab_to_CondensedSet.obj A).val.obj T) :=
show add_comm_group (A.val.obj T), by apply_instance

lemma free_pfpng_ext (u v : S.free_pfpng)
  (huv : ∀ T : discrete_quotient S, S.free_pfpng_π T u = S.free_pfpng_π T v) : u = v :=
begin
  let E : limits.cone (S.fintype_diagram ⋙ free_pfpng_functor) :=
    ProFiltPseuNormGrp₁.bounded_cone
    ⟨Ab.explicit_limit_cone _, Ab.explicit_limit_cone_is_limit _⟩,
  let hE : limits.is_limit E := ProFiltPseuNormGrp₁.bounded_cone_is_limit _,
  let ee : S.free_pfpng ≅ E.X := (limits.limit.is_limit _).cone_point_unique_up_to_iso hE,
  apply_fun ee.hom, swap,
  { intros x y hh, apply_fun ee.inv at hh, simpa using hh },
  ext T : 3, exact huv T,
end

variables (x : S.pmz ⌊j⌋₊) (T : discrete_quotient S)

lemma lhs_helper : (S.free_pfpng_π T) ((S.pmz_to_free_pfpng j) x).1 =
  ∑ i : fin ⌊j⌋₊, pi.single (T.proj (x.2 i)) (x.1.down i : ℤ) :=
begin
  change (((S.pmz_to_free_pfpng _) ≫ (ProFiltPseuNormGrp₁.level.obj j).map
    (S.free_pfpng_π T)) _).val = _,
  dsimp [Profinite.pmz_to_free_pfpng, Profinite.free_pfpng_π],
  erw ← comp_apply,
  erw limits.is_limit.fac,
  dsimp [Profinite.pmz_to_level_nat_trans, Profinite.pmz_to_level],
  rcases x with ⟨x1,x2⟩,
  dsimp [Profinite.pmz_cone, Profinite.sigma.desc, Profinite.pmz_to_level_component,
    Profinite.pmz_functor, Profinite.product.lift, Profinite.sigma.ι],
  congr' 1, ext i t, erw pi.single_apply,
  split_ifs with h1 h2 h3 h4,
  { refl },
  { exact false.elim (h2 h1.symm) },
  { exact false.elim (h1 h3.symm) },
  { refl }
end

lemma rhs_helper₁ :
  (λ (f : ulift (fin ⌊j⌋₊ → sign_type)),
  ∑ (x : fin ⌊j⌋₊),
    ((proetale_topology.to_sheafify (S.to_Condensed.val ⋙ AddCommGroup.free')).app
      (op (S.pow ⌊j⌋₊)))
      (finsupp.single {down := Profinite.product.π (λ (i : fin ⌊j⌋₊), S) x} ↑(f.down x))) =
  ∑ (x : fin ⌊j⌋₊), (λ f, (proetale_topology.to_sheafify
    (S.to_Condensed.val ⋙ AddCommGroup.free')).app (op (S.pow ⌊j⌋₊)) $
    finsupp.single ⟨Profinite.product.π _ x⟩ (f.down x)) := by { ext, simp }

lemma _root_.CompHausFiltPseuNormGrp.to_Condensed_app_sum_apply (n : ℕ)
  (A : CompHausFiltPseuNormGrp.{u}) (T : Profinite.{u})
    (g : fin n → (CompHausFiltPseuNormGrp.to_Condensed.obj A).val.obj (op T)) (t : T) :
  (ulift.down (∑ i : fin n, g i)).1 t = ∑ i : fin n,
    (ulift.down (g i)).1 t := sorry

lemma rhs_helper₃ (i : fin ⌊j⌋₊) :
  ((((S.free'_lift S.to_condensed_free_pfpng).val.app (op (S.pmz ⌊j⌋₊)))
    (((Condensed.val_obj_sigma_add_equiv (λ (f : ulift (fin ⌊j⌋₊ → sign_type)), S.pow ⌊j⌋₊)
      S.free').symm)
    (λ (f : ulift (fin ⌊j⌋₊ → sign_type)),
      ((proetale_topology.to_sheafify (S.to_Condensed.val ⋙ AddCommGroup.free')).app
      (op (S.pow ⌊j⌋₊)))
      (finsupp.single {down := Profinite.product.π (λ (i : fin ⌊j⌋₊), S) i}
        ↑(f.down i))))).down).1 x =
    (x.1.down i : ℤ) • (S.to_free_pfpng (x.2 i)).1 := sorry

lemma rhs_helper₂ (i : fin ⌊j⌋₊) : (S.free_pfpng_π T)
  (((((S.free'_lift S.to_condensed_free_pfpng).val.app (op (S.pmz ⌊j⌋₊)))
    (((Condensed.val_obj_sigma_add_equiv (λ (f : ulift (fin ⌊j⌋₊ → sign_type)), S.pow ⌊j⌋₊)
      S.free').symm)
    (λ (f : ulift (fin ⌊j⌋₊ → sign_type)),
      ((proetale_topology.to_sheafify (S.to_Condensed.val ⋙ AddCommGroup.free')).app
      (op (S.pow ⌊j⌋₊)))
      (finsupp.single {down := Profinite.product.π (λ (i : fin ⌊j⌋₊), S) i}
        ↑(f.down i))))).down).1 x) =
  pi.single (T.proj (x.snd i)) ↑(x.fst.down i) :=
begin
  rw rhs_helper₃,
  erw (S.free_pfpng_π T).to_add_monoid_hom.map_zsmul,
  change
    _ • (((S.to_free_pfpng) ≫ (ProFiltPseuNormGrp₁.level.obj 1).map (S.free_pfpng_π T)) _).val = _,
  dsimp [Profinite.to_free_pfpng, Profinite.free_pfpng_π,
    Profinite.free_pfpng_level_iso],
  dsimp [limits.is_limit.cone_point_unique_up_to_iso],
  erw ← comp_apply,
  erw ← comp_apply,
  erw limits.is_limit.fac,
  erw limits.is_limit.fac,
  dsimp [Fintype.free_pfpng_unit, Profinite.as_limit_cone],
  ext t, erw pi.single_apply, split_ifs; simp,
  { intros hh, exact false.elim (hh h.symm) },
  { intros hh, exact false.elim (h hh.symm) },
end

lemma rhs_helper :
  (S.free_pfpng_π T)
  ((((S.free'_lift S.to_condensed_free_pfpng).val.app (op (S.pmz ⌊j⌋₊)))
  ((S.pmz_to_free' ⌊j⌋₊).val.app (op (S.pmz ⌊j⌋₊)) {down := 𝟙 (S.pmz ⌊j⌋₊)})).1.1 x) =
  ∑ i : fin ⌊j⌋₊, pi.single (T.proj (x.2 i)) (x.1.down i : ℤ) :=
begin
  dsimp [Profinite.pmz_to_free'],
  rw [category_theory.functor.map_id, id_apply],
  simp only [add_monoid_hom.map_sum],
  rw [rhs_helper₁],
  rw [add_equiv.map_sum, add_monoid_hom.map_sum],
  have := _root_.CompHausFiltPseuNormGrp.to_Condensed_app_sum_apply ⌊j⌋₊ _ _ _ x,
  dsimp at this, erw this, clear this,
  erw (S.free_pfpng_π T).to_add_monoid_hom.map_sum,
  congr' 1, funext i, dsimp,
  erw rhs_helper₂,
end

lemma key (j : (ulift.{u+1} nnreal)) :
  Profinite_to_Condensed.map (S.pmz_to_free_pfpng j.down) ≫
    (CompHausFiltPseuNormGrp₁.enlarging_functor.obj
    (ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng)).level_Condensed_diagram_cocone.ι.app j =
  S.pmz_to_free' ⌊j.down⌋₊ ≫
  Condensed_Ab_to_CondensedSet.map S.free'_to_condensed_free_pfpng :=
begin
  apply_fun Profinite.to_Condensed_equiv _ _,
  ext x : 3, dsimp at x,
  dsimp [CompHausFiltPseuNormGrp.level_Condensed_diagram_cocone,
    Profinite.free'_to_condensed_free_pfpng],
  apply free_pfpng_ext, intros T,
  erw lhs_helper, erw rhs_helper,
end

end Profinite.epi_free'_to_condensed_setup

instance Profinite.epi_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : epi S.free'_to_condensed_free_pfpng :=
begin
  apply faithful_reflects_epi (Condensed_Ab_to_CondensedSet),
  let E := CompHausFiltPseuNormGrp.level_Condensed_diagram_cocone
    (CompHausFiltPseuNormGrp₁.enlarging_functor.obj
    ((ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng))),
  have hh : is_iso (limits.colimit.desc _ E),
  { change is_iso (CompHausFiltPseuNormGrp.colimit_to_Condensed_obj _),
    apply_instance },
  let hE : limits.is_colimit E := @limits.is_colimit.of_point_iso
    _ _ _ _ _ _ _ _ hh, -- <-- move this
  apply category_theory.epi_to_colimit_of_exists  _ E hE,
  intros j,
  let j' : nnreal := ulift.down j,
  use [(S.pmz ⌊j'⌋₊).to_Condensed, S.pmz_to_free' ⌊j'⌋₊,
    Profinite_to_Condensed.map (S.pmz_to_free_pfpng j')],
  split,
  { apply epi_Profinite_to_Condensed_map_of_epi },
  { apply Profinite.epi_free'_to_condensed_setup.key },
end
