import free_pfpng.setup

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

section
variables {α : Type*} [decidable_eq α] [nonempty α]

open finset

-- TODO: Inlining this yields an app-builder exception
lemma exists_signed_sum_aux {n : ℕ} (sgn : ℕ → sign_type) (b : α) [decidable_eq α]
  {f : α → ℤ}
  ⦃a : α⦄ (g : ℕ → α) (i : ℕ) :
  ite ((range (n - (f a).nat_abs)).piecewise g (λ _, a) i = b)
        ((range (n - (f a).nat_abs)).piecewise sgn (λ _, sign (f a)) i : ℤ) 0 =
    (range (n - (f a).nat_abs)).piecewise (λ j, ite (g j = b) ↑(sgn j) 0)
        (λ j, ite (a = b) ↑(sign (f a)) 0) i :=
by { unfold piecewise, split_ifs; refl }

lemma exists_signed_sum (s : finset α) (n : ℕ) (f : α → ℤ) (hn : ∑ i in s, (f i).nat_abs ≤ n) :
  ∃ (sgn : ℕ → sign_type) (g : ℕ → α), (∀ i, g i ∉ s → sgn i = 0) ∧
    ∀ a ∈ s, (∑ i in range n, if g i = a then (sgn i : ℤ) else 0) = f a :=
begin
  induction s using finset.cons_induction with a s ha ih generalizing n,
  { exact ⟨0, classical.arbitrary _, λ _ _, rfl, λ _, false.elim⟩ },
  rw sum_cons at hn,
  obtain ⟨sgn, g, hg, hf⟩ := ih _ (le_tsub_of_add_le_left hn),
  refine ⟨(range $ n - (f a).nat_abs).piecewise sgn (λ _, sign (f a)),
    (range $ n - (f a).nat_abs).piecewise g (λ _, a), λ i hi, _, λ b hb, _⟩,
  { by_cases i ∈ range (n - (f a).nat_abs),
    { rw piecewise_eq_of_mem _ _ _ h at ⊢ hi,
      exact hg _ (λ h, hi $ subset_cons _ h) },
    { rw piecewise_eq_of_not_mem _ _ _ h at hi,
      exact (hi $ mem_cons_self _ _).elim } },
  transitivity ∑ i in range n, (range $ n - (f a).nat_abs).piecewise
    (λ j, ite (g j = b) (sgn j : ℤ) 0) (λ j, ite (a = b) (sign $ f a) 0) i,
  { exact sum_congr rfl (λ i _, exists_signed_sum_aux _ _ _ _) },
  rw [sum_piecewise, (inter_eq_right_iff_subset _ _).2 (range_mono tsub_le_self)],
  rw mem_cons at hb,
  obtain rfl | hb := hb,
  { rw [sum_eq_zero, zero_add, sum_const, if_pos rfl, card_sdiff (range_mono tsub_le_self),
      card_range, card_range, tsub_tsub_cancel_of_le
        (nat.le_of_add_le_left hn), nsmul_eq_mul, mul_comm,
      ←int.sign_eq_sign, int.nat_cast_eq_coe_nat, (f b).sign_mul_nat_abs],
    refine λ i hi, ite_eq_right_iff.2 _,
    rintro rfl,
    rw [hg _ ha, sign_type.coe_zero] },
  { simp_rw [if_neg (ne_of_mem_of_not_mem hb ha).symm, hf _ hb, sum_const_zero, add_zero] }
end

lemma Profinite.pmz_to_free_pfpng_epi_aux' [fintype α]
  (r : nnreal) (f : α → ℤ) (hf : ∑ i : α, ∥f i∥₊ ≤ r) :
  ∃ (sgn : ℕ → sign_type) (g : ℕ → α),
    ∀ t, (∑ i in range ⌊r⌋₊, if g i = t then (sgn i : ℤ) else 0) = f t :=
begin
  refine Exists₂.imp (λ _ _ h t, _) (exists_signed_sum univ ⌊r⌋₊ f _),
  { exact h.2 t (mem_univ _) },
  refine nat.le_floor _,
  simp_rw [nat.cast_sum, nnreal.coe_nat_abs],
  exact hf,
end

lemma Profinite.pmz_to_free_pfpng_epi_aux [fintype α]
  (r : nnreal) (f : α → ℤ) (hf : ∑ i : α, ∥f i∥₊ ≤ r) :
  ∃ (sgn : fin ⌊r⌋₊ → sign_type) (g : fin ⌊r⌋₊ → α),
    (∑ i : fin ⌊r⌋₊, (λ t : α, if g i = t then (sgn i : ℤ) else 0)) = f :=
begin
  obtain ⟨e,g,h⟩ := Profinite.pmz_to_free_pfpng_epi_aux' r f hf,
  let e' : fin ⌊r⌋₊ → sign_type := λ i, e i.1,
  let g' : fin ⌊r⌋₊ → α := λ i, g i.1,
  use [e',g'],
  ext t, rw ← h,
  simp only [finset.sum_apply],
  rw finset.sum_range, refl,
end

end

-- Move this
instance discrete_quotient.nonempty (X : Type*) [topological_space X] [h : nonempty X]
  (T : discrete_quotient X) : nonempty T := ⟨T.proj (nonempty.some h)⟩

instance Profinite.pmz_to_free_pfpng_epi (S : Profinite.{u}) [nonempty S] (j : nnreal) :
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
  exact ht,
end

.

namespace Profinite.epi_free'_to_condensed_setup

variables (S : Profinite.{u}) (j : nnreal)

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
    ⟨Ab.explicit_limit_cone.{u u} _, Ab.explicit_limit_cone_is_limit _⟩,
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

def _root_.CompHausFiltPseuNormGrp.coe_add_monoid_hom
  (A : CompHausFiltPseuNormGrp.{u}) (T : Profinite.{u}) :
  (CompHausFiltPseuNormGrp.to_Condensed.obj A).val.obj (op T) →+ T → A :=
{ to_fun := λ f, f.down.1,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

lemma _root_.CompHausFiltPseuNormGrp.to_Condensed_app_sum_apply (n : ℕ)
  (A : CompHausFiltPseuNormGrp.{u}) (T : Profinite.{u})
    (g : fin n → (CompHausFiltPseuNormGrp.to_Condensed.obj A).val.obj (op T)) (t : T) :
  (ulift.down (∑ i : fin n, g i)).1 t = ∑ i : fin n,
    (ulift.down (g i)).1 t :=
begin
  let e := A.coe_add_monoid_hom T,
  change _ = ∑ (i : fin n), (e (g i)) t,
  rw [← finset.sum_apply t finset.univ (λ i : fin n, (e (g i))), ← e.map_sum],
  refl,
end

lemma Profinite.free'_lift_val_obj_sigma_equiv_symm {α : Type u} [fintype α]
  (A : Condensed.{u} Ab.{u+1}) (η : S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj A)
  (X : α → Profinite.{u}) (t) :
  (S.free'_lift η).val.app (op $ Profinite.sigma X)
  ((Condensed.val_obj_sigma_add_equiv _ _ ).symm t) =
  (Condensed.val_obj_sigma_add_equiv _ _ ).symm (λ a, (S.free'_lift η).val.app _ (t a)) :=
begin
  apply_fun Condensed.val_obj_sigma_add_equiv (λ (a : α), X a) A,
  simp only [add_equiv.apply_symm_apply],
  funext a,
  dsimp,
  simp only [← comp_apply, ← nat_trans.naturality],
  simp only [comp_apply],
  congr' 1,
  rw ← Condensed.val_obj_sigma_add_equiv_apply_apply,
  simp only [add_equiv.apply_symm_apply],
end

-- move and rename
def rhs_helper_equiv
  (A : ProFiltPseuNormGrp₁.{u}) :
  A ≃ (CompHausFiltPseuNormGrp.to_Condensed.obj
    (CHFPNG₁_to_CHFPNGₑₗ.obj
      (PFPNG₁_to_CHFPNG₁ₑₗ.obj A))).val.obj
      (op Profinite.punit) :=
{ to_fun := λ a, ulift.up $ ⟨λ _, a, begin
    obtain ⟨c,hc⟩ := ProFiltPseuNormGrp₁.exhaustive _ a,
    refine ⟨c, λ _, ⟨a,hc⟩, _, rfl⟩,
    apply continuous_of_discrete_topology
  end⟩,
  inv_fun := λ f, f.down.val punit.star,
  left_inv := λ t, rfl,
  right_inv := λ t, by { ext ⟨⟩, refl } }

-- move and rename
def rhs_helper_equiv' :
  S ≃ S.to_Condensed.val.obj (op Profinite.punit) :=
{ to_fun := λ s, ulift.up $ Profinite.pt s,
  inv_fun := λ s, (ulift.down s).1 punit.star,
  left_inv := λ t, rfl,
  right_inv := λ t, by { ext ⟨⟩, refl } }

lemma rhs_helper₄ {α : Type u} [fintype α]
  (A : ProFiltPseuNormGrp₁.{u})
  (X : α → Profinite.{u})
  (e : Π (a : α),
    (CompHausFiltPseuNormGrp.to_Condensed.obj
    (CHFPNG₁_to_CHFPNGₑₗ.obj
      (PFPNG₁_to_CHFPNG₁ₑₗ.obj A))).val.obj (op $ X a))
  (a₀ : α) (x₀ : X a₀) :
  ((Condensed.val_obj_sigma_add_equiv X _).symm e).down.val ⟨a₀,x₀⟩ =
  (e a₀).down.val x₀ :=
begin
  let B := Condensed_Ab_to_CondensedSet.obj
    (CompHausFiltPseuNormGrp.to_Condensed.obj
    (CHFPNG₁_to_CHFPNGₑₗ.obj
      (PFPNG₁_to_CHFPNG₁ₑₗ.obj A))) ,
  let e₀ : (X a₀).to_Condensed ⟶ B :=
    (Profinite.to_Condensed_equiv _ B).symm (e a₀),
  let ee : (Profinite.sigma X).to_Condensed ⟶ B :=
    (Profinite.to_Condensed_equiv _ B).symm ((Condensed.val_obj_sigma_add_equiv X _).symm e),
  apply_fun rhs_helper_equiv A,
  let s₀ : (X a₀).to_Condensed.val.obj (op Profinite.punit) :=
    rhs_helper_equiv' _ x₀,
  have : (rhs_helper_equiv A) ((e a₀).down.val x₀) =
    e₀.val.app _ s₀, refl,
  rw this,
  have : e₀ = (Profinite_to_Condensed.map (Profinite.sigma.ι X a₀)) ≫ ee,
  { dsimp only [e₀, ee], symmetry,
    apply _root_.Condensed.val_obj_sigma_add_equiv_symm_apply },
  rw this, refl,
end

lemma rhs_helper₃ (i : fin ⌊j⌋₊) :
  ((((S.free'_lift S.to_condensed_free_pfpng).val.app (op (S.pmz ⌊j⌋₊)))
    (((Condensed.val_obj_sigma_add_equiv (λ (f : ulift (fin ⌊j⌋₊ → sign_type)), S.pow ⌊j⌋₊)
      S.free').symm)
    (λ (f : ulift (fin ⌊j⌋₊ → sign_type)),
      ((proetale_topology.to_sheafify (S.to_Condensed.val ⋙ AddCommGroup.free')).app
      (op (S.pow ⌊j⌋₊)))
      (finsupp.single {down := Profinite.product.π (λ (i : fin ⌊j⌋₊), S) i}
        ↑(f.down i))))).down).1 x =
    (x.1.down i : ℤ) • (S.to_free_pfpng (x.2 i)).1 :=
begin
  erw Profinite.free'_lift_val_obj_sigma_equiv_symm,
  simp only [← comp_apply],
  erw [free'_lift_app_eq'],
  simp only [continuous_map.to_fun_eq_coe, linear_map.to_add_monoid_hom_coe, finsupp.lift_apply,
  Profinite.to_condensed_free_pfpng_app, finsupp.sum_single_index, zero_smul, subtype.val_eq_coe],
  -- This is now very close...
  let Q := Condensed.val_obj_sigma_add_equiv (λ (a : ulift (fin ⌊j⌋₊ → sign_type)), S.pow ⌊j⌋₊)
    S.condensed_free_pfpng,
  change (Q.symm _).down.1 _ = _,
  cases x with x1 x2,
  erw rhs_helper₄,
  refl,
end

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
    (CHFPNG₁_to_CHFPNGₑₗ.obj
    (PFPNG₁_to_CHFPNG₁ₑₗ.obj S.free_pfpng)).level_Condensed_diagram_cocone.ι.app j =
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

instance Profinite.epi_free'_to_condensed_free_pfpng_of_nonempty
  (S : Profinite.{u}) [nonempty S] : epi S.free'_to_condensed_free_pfpng :=
begin
  apply faithful_reflects_epi (Condensed_Ab_to_CondensedSet),
  let E := CompHausFiltPseuNormGrp.level_Condensed_diagram_cocone
    (CHFPNG₁_to_CHFPNGₑₗ.obj
    ((PFPNG₁_to_CHFPNG₁ₑₗ.obj S.free_pfpng))),
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
