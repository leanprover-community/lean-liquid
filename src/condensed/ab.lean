import category_theory.abelian.projective
import pseudo_normed_group.category
import topology.continuous_function.algebra

import algebra.group.ulift

import for_mathlib.abelian_sheaves.main
import for_mathlib.AddCommGroup.exact

import condensed.adjunctions
import condensed.top_comparison
import condensed.filtered_colimits

/-!
# Properties of the category of condensed abelian groups

-/

open category_theory category_theory.limits

universes v u

-- Move this!
-- @[simps obj map {fully_applied := ff}] -- we probably don't want these as global simp lemmas
def Ab.ulift : Ab.{u} ⥤ Ab.{max v u} :=
{ obj := λ M, AddCommGroup.of $ ulift.{v} M,
  map := λ M N f,
  { to_fun := λ x, ⟨f x.down⟩,
    map_zero' := by { ext1, apply f.map_zero },
    map_add' := λ x y, by { ext1, apply f.map_add } },
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

@[simp] lemma Ab.exact_ulift_map {A B C : Ab} (f : A ⟶ B) (g : B ⟶ C) :
  exact (Ab.ulift.map f) (Ab.ulift.map g) ↔ exact f g :=
begin
  let F := Ab.ulift.map f,
  let G := Ab.ulift.map g,
  change exact F G ↔ _,
  rw AddCommGroup.exact_iff,
  rw AddCommGroup.exact_iff,
  split,
  { intro h,
    apply le_antisymm,
    { rintros _ ⟨x,rfl⟩,
      have : ulift.up (f x) ∈ F.range := ⟨⟨x⟩, rfl⟩,
      rw h at this,
      change _ = _ at this,
      apply_fun (λ e, e.down) at this,
      exact this },
    { rintros x hx, change _ = _ at hx,
      have : ulift.up x ∈ G.ker, by { apply_fun ulift.up at hx, exact hx },
      rw ← h at this,
      obtain ⟨y,hy⟩ := this,
      apply_fun (λ e, e.down) at hy,
      rw ← hy,
      use [y.down, rfl] } },
  { intro h,
    apply le_antisymm,
    { rintros _ ⟨x,rfl⟩,
      ext,
      change _ ∈ g.ker,
      rw ← h,
      use [x.down, rfl] },
    { intros x hx,
      change _ = _ at hx,
      apply_fun (λ e, e.down) at hx,
      change _ ∈ g.ker at hx,
      rw ← h at hx,
      obtain ⟨y,hy⟩ := hx,
      use y,
      ext,
      exact hy } },
end

namespace Condensed

--instance : preadditive (Condensed Ab.{u+1}) := by admit

noncomputable theory

-- Sanity check
example {J : Type (u+1)} [small_category J] [is_filtered J] :
  limits.preserves_colimits_of_shape J (forget Ab.{u+1}) := by apply_instance

-- this is now available in `condensed/projective_resolutions.lean`...
--instance : enough_projectives (Condensed Ab.{u+1}) := by admit

instance : is_right_adjoint (Sheaf_to_presheaf _ _ : Condensed Ab.{u+1} ⥤ _) :=
{ left := presheaf_to_Sheaf _ _,
  adj := (sheafification_adjunction _ _) }

@[simps obj map {fully_applied := ff}]
def forget_to_CondensedType : Condensed Ab.{u+1} ⥤ CondensedSet :=
{ obj := λ F, ⟨F.val ⋙ forget _, begin
    cases F with F hF,
    rwa (presheaf.is_sheaf_iff_is_sheaf_forget _ _ (forget Ab)) at hF,
    apply_instance
  end ⟩,
  map := λ A B f, ⟨whisker_right f.val _⟩ }

instance : is_right_adjoint forget_to_CondensedType :=
{ left := CondensedSet_to_Condensed_Ab,
  adj := Condensed_Ab_CondensedSet_adjunction }

section

variables (A : Type u) [add_comm_group A] [topological_space A] [topological_add_group A]

def of_top_ab.presheaf : Profinite.{u}ᵒᵖ ⥤ Ab.{u} :=
{ obj := λ S, ⟨C(S.unop, A)⟩,
  map := λ S₁ S₂ f, add_monoid_hom.mk' (λ g, g.comp f.unop) $ λ g₁ g₂, rfl,
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

/-- The condensed abelian group associated with a topological abelian group -/
def of_top_ab : Condensed.{u} Ab.{u+1} :=
{ val := of_top_ab.presheaf A ⋙ Ab.ulift.{u+1},
  cond := begin
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (forget Ab),
    swap, apply_instance,
    let B := Top.of A,
    change presheaf.is_sheaf _ B.to_Condensed.val,
    exact B.to_Condensed.cond,
  end }


variables {A} {B : Type u} [add_comm_group B] [topological_space B] [topological_add_group B]

def of_top_ab_map (f : A →+ B) (hf : continuous f) : of_top_ab A ⟶ of_top_ab B :=
{ val := whisker_right
  { app := λ S, begin
      refine add_monoid_hom.mk' (λ g, ⟨f ∘ (show C(↥(opposite.unop S), A), from g), hf.comp _⟩) _,
      { exact g.continuous },
      { intros, ext, exact f.map_add _ _, }
    end,
    naturality' := λ S T g, rfl, }
  Ab.ulift.{u+1} }


end

end Condensed

namespace CompHausFiltPseuNormGrp

open_locale nnreal
open pseudo_normed_group comphaus_filtered_pseudo_normed_group

def presheaf (A : CompHausFiltPseuNormGrp.{u}) (S : Profinite.{u}) : Type u :=
{ f : S → A // ∃ (c : ℝ≥0) (f₀ : S → filtration A c), continuous f₀ ∧ f = coe ∘ f₀ }

namespace presheaf

variables (A : CompHausFiltPseuNormGrp.{u}) (S : Profinite.{u})

@[ext]
lemma ext {A : CompHausFiltPseuNormGrp} {S : Profinite} (f g : presheaf A S) : f.1 = g.1 → f = g :=
subtype.ext

instance : has_zero (presheaf A S) := ⟨⟨0, 0, 0, continuous_zero, rfl⟩⟩

instance : has_neg (presheaf A S) :=
⟨λ f, ⟨-f.1,
  begin
    obtain ⟨_, c, f, hf, rfl⟩ := f,
    refine ⟨c, λ s, - f s, _, rfl⟩,
    exact (continuous_neg' c).comp hf
  end⟩⟩

instance : has_add (presheaf A S) :=
⟨λ f g, ⟨f.1 + g.1,
  begin
    obtain ⟨_, cf, f, hf, rfl⟩ := f,
    obtain ⟨_, cg, g, hg, rfl⟩ := g,
    refine ⟨cf + cg, λ s, ⟨f s + g s, add_mem_filtration (f s).2 (g s).2⟩, _, rfl⟩,
    have aux := (hf.prod_mk hg),
    exact (continuous_add' cf cg).comp aux,
  end⟩⟩

instance : has_sub (presheaf A S) :=
⟨λ f g, ⟨f.1 - g.1,
  begin
    obtain ⟨_, cf, f, hf, rfl⟩ := f,
    obtain ⟨_, cg, g, hg, rfl⟩ := g,
    refine ⟨cf + cg, λ s, ⟨f s - g s, sub_mem_filtration (f s).2 (g s).2⟩, _, rfl⟩,
    have aux := (hf.prod_mk ((continuous_neg' cg).comp hg)),
    simp only [sub_eq_add_neg],
    exact (continuous_add' cf cg).comp aux,
  end⟩⟩

variables {A S}

protected def nsmul (n : ℕ) (f : presheaf A S) : presheaf A S :=
⟨n • f.1,
begin
  obtain ⟨_, c, f, hf, rfl⟩ := f,
  refine ⟨n * c, λ s, ⟨n • f s, nat_smul_mem_filtration _ _ _ (f s).2⟩, _, rfl⟩,
  exact continuous_nsmul _ _ _ hf,
end⟩

protected def zsmul (n : ℤ) (f : presheaf A S) : presheaf A S :=
⟨n • f.1,
begin
  obtain ⟨_, c, f, hf, rfl⟩ := f,
  refine ⟨n.nat_abs * c, λ s, ⟨n • f s, int_smul_mem_filtration _ _ _ (f s).2⟩, _, rfl⟩,
  exact continuous_zsmul _ _ _ hf,
end⟩

variables (A S)

instance : add_comm_group (presheaf A S) :=
{ zero := 0,
  add := (+),
  nsmul := presheaf.nsmul,
  zsmul := presheaf.zsmul,
  add_assoc := by { intros, ext, exact add_assoc _ _ _ },
  zero_add := by { intros, ext, exact zero_add _ },
  add_zero := by { intros, ext, exact add_zero _ },
  add_comm := by { intros, ext, exact add_comm _ _ },
  add_left_neg := by { intros, ext, exact add_left_neg _ },
  sub_eq_add_neg := by { intros, ext, exact sub_eq_add_neg _ _ },
  nsmul_zero' := by { intros, ext, exact zero_nsmul _ },
  nsmul_succ' := by { intros, ext, exact succ_nsmul _ _ },
  zsmul_zero' := by { intros, ext, exact zero_zsmul _ },
  zsmul_succ' := by { intros, ext, exact add_comm_group.zsmul_succ' _ _ },
  zsmul_neg' := by { intros, ext, exact add_comm_group.zsmul_neg' _ _ },
  .. presheaf.has_sub A S, .. presheaf.has_neg A S }

@[simps apply {fully_applied := ff}]
def comap (A : CompHausFiltPseuNormGrp) {S T : Profinite} (φ : S ⟶ T) :
  presheaf A T →+ presheaf A S :=
{ to_fun := λ f, ⟨f.1 ∘ φ,
  begin
    obtain ⟨_, c, f, hf, rfl⟩ := f,
    refine ⟨c, f ∘ φ, hf.comp φ.continuous, rfl⟩,
  end⟩,
  map_zero' := rfl,
  map_add' := by { intros, refl } }

@[simps apply {fully_applied := ff}]
def map {A B : CompHausFiltPseuNormGrp} (φ : A ⟶ B) (S : Profinite) :
  presheaf A S →+ presheaf B S :=
{ to_fun := λ f, ⟨φ ∘ f.1,
  begin
    obtain ⟨_, c, f, hf, rfl⟩ := f,
    obtain ⟨d,hd⟩ := φ.bound,
    let e : filtration A c → filtration B (d * c) := λ t, ⟨φ t, hd t.2⟩,
    have he : continuous e,
    { apply φ.continuous, intros, refl },
    refine ⟨d * c, e ∘ f, he.comp hf, rfl⟩,
  end⟩,
  map_zero' := by { ext, exact φ.map_zero },
  map_add' := by { intros, ext, exact φ.map_add _ _ } }

end presheaf

open opposite

@[simps obj map {fully_applied := ff}]
def Presheaf (A : CompHausFiltPseuNormGrp.{u}) : Profinite.{u}ᵒᵖ ⥤ Ab :=
{ obj := λ S, ⟨presheaf A (unop S)⟩,
  map := λ S T φ, presheaf.comap A φ.unop,
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

@[simps app {fully_applied := ff}]
def Presheaf.map {A B : CompHausFiltPseuNormGrp} (φ : A ⟶ B) :
  Presheaf A ⟶ Presheaf B :=
{ app := λ S, presheaf.map φ (unop S),
  naturality' := by { intros, refl } }

@[simp]
lemma Presheaf.map_id (A : CompHausFiltPseuNormGrp) :
  Presheaf.map (𝟙 A) = 𝟙 _ := by { ext, refl }

@[simp]
lemma Presheaf.map_comp {A B C : CompHausFiltPseuNormGrp} (f : A ⟶ B) (g : B ⟶ C) :
  Presheaf.map (f ≫ g) = Presheaf.map f ≫ Presheaf.map g := by { ext, refl }

set_option pp.universes true

lemma Presheaf_comp_ulift_is_sheaf_aux_equalizer
  (A : CompHausFiltPseuNormGrp.{u}) :
  (A.Presheaf ⋙ Ab.ulift.{u+1 u} ⋙ forget.{u+2 u+1 u+1} Ab.{u+1}).equalizer_condition :=
begin
  intros X B π hh,
  split,
  { rintros ⟨x⟩ ⟨y⟩ h,
    ext t,
    obtain ⟨t,rfl⟩ := hh t,
    apply_fun (λ e, e.val.down.val t) at h,
    exact h },
  { rintros ⟨⟨⟨t,c,t',ht',ht⟩⟩,h⟩,
    let E : Top := Top.of (filtration A c),
    let t'' : Profinite.to_Top.obj X ⟶ E := ⟨t',ht'⟩,
    have hw : Profinite.to_Top.{u}.map (Profinite.pullback.fst.{u} π π) ≫ t'' =
      Profinite.to_Top.{u}.map (Profinite.pullback.snd.{u} π π) ≫ t'',
    { dsimp at h,
      ext i,
      dsimp [Profinite.pullback.fst, Profinite.pullback.snd],
      apply_fun (λ e, e.down.val i) at h,
      change (coe ∘ t') i.val.fst = (coe ∘ t') i.val.snd,
      rw ← ht,
      exact h },
    let w := Profinite.descend_to_Top π t'' hh hw,
    refine ⟨⟨⟨_,c,w,w.2,rfl⟩⟩,_⟩,
    ext : 3,
    dsimp,
    rw ht,
    ext i,
    dsimp [CompHausFiltPseuNormGrp.Presheaf, Ab.ulift,
      functor.map_to_equalizer],
    have := Profinite.π_descend_to_Top π t'' hh hw,
    apply_fun (λ e, (e i).val) at this, exact this }
end

lemma Presheaf_comp_ulift_is_sheaf (A : CompHausFiltPseuNormGrp.{u}):
  presheaf.is_sheaf proetale_topology (Presheaf A ⋙ Ab.ulift.{u+1}) :=
begin
  rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (forget Ab),
  swap, apply_instance,
  rw is_sheaf_iff_is_sheaf_of_type,
  erw (functor.is_proetale_sheaf_of_types_tfae
    (A.Presheaf ⋙ Ab.ulift.{u+1} ⋙ forget _)).out 0 5,
  refine ⟨_,_,_⟩,
  { dsimp [functor.empty_condition],
    split,
    { intros a b h, ext ⟨⟩ },
    { intros x, dsimp,
      refine ⟨⟨⟨λ x, x.elim, 0, λ x, x.elim, by continuity, _⟩⟩, _⟩,
      { ext ⟨⟩ },
      { cases x, refl } } },
  { intros X Y,
    split,
    { rintros ⟨x⟩ ⟨y⟩ h, dsimp at h,
      ext : 2,
      dsimp,
      ext (t|t),
      { apply_fun (λ e, e.fst.down.val t) at h, exact h },
      { apply_fun (λ e, e.snd.down.val t) at h, exact h } },
    { rintros ⟨⟨f,c,f',hf',hf⟩,⟨g,d,g',hg',hg⟩⟩,
      let p : X.sum Y → A := λ t, sum.rec_on t f g,
      let e : ℝ≥0 := c ⊔ d,
      haveI : fact (c ≤ e) := ⟨le_sup_left⟩,
      haveI : fact (d ≤ e) := ⟨le_sup_right⟩,
      let p' : X.sum Y → filtration A e :=
        λ t, sum.rec_on t (cast_le ∘ f') (cast_le ∘ g'),
      have hp' : continuous p',
      { apply continuous_sup_dom,
        { apply continuous_coinduced_dom,
          have : p' ∘ sum.inl = cast_le ∘ f', by ext; refl,
          rw this,
          apply continuous.comp _ hf',
          apply continuous_cast_le },
        { apply continuous_coinduced_dom,
          have : p' ∘ sum.inr = cast_le ∘ g', by ext; refl,
          rw this,
          apply continuous.comp _ hg',
          apply continuous_cast_le } },
      have hh : p = coe ∘ p',
      { ext (a|a),
        { apply_fun (λ u, u a) at hf, exact hf },
        { apply_fun (λ u, u a) at hg, exact hg } },
      refine ⟨⟨⟨p,e,p',hp',hh⟩⟩,_⟩,
      ext; refl } },
  { apply Presheaf_comp_ulift_is_sheaf_aux_equalizer }
end

@[simps obj map {fully_applied := ff}]
def to_Condensed : CompHausFiltPseuNormGrp.{u} ⥤ Condensed.{u} Ab.{u+1} :=
{ obj := λ A,
  { val := Presheaf A ⋙ Ab.ulift.{u+1},
    cond := Presheaf_comp_ulift_is_sheaf _ },
  map := λ A B f, ⟨whisker_right (Presheaf.map f) _⟩,
  map_id' := λ X, by { ext : 2, dsimp, simp },
  map_comp' := λ X Y Z f g, by { ext : 2, dsimp, simp } }

section

-- #check Top.to_Condensed

variables (A : CompHausFiltPseuNormGrp.{u})

@[simps]
def level_CompHaus_diagram : ℝ≥0 ⥤ CompHaus.{u} :=
{ obj := λ r, CompHaus.of $ filtration A r,
  map := λ r s h,
  { to_fun := cast_le' h.le,
    continuous_to_fun := by letI : fact (r ≤ s) := ⟨h.le⟩; exact continuous_cast_le _ _ },
  map_id' := λ r, by { ext, refl },
  map_comp' := λ r s t h1 h2, by { ext, refl } }

@[simps]
def level_Condensed_diagram : ℝ≥0 ⥤ CondensedSet.{u} :=
A.level_CompHaus_diagram ⋙ CompHaus_to_Top.{u} ⋙ Top_to_Condensed.{u}

@[simps]
def level_Condensed_diagram' : (as_small.{u+1} ℝ≥0) ⥤ CondensedSet.{u} :=
as_small.down ⋙ A.level_Condensed_diagram

def level_Condensed_diagram_cone :
  cocone A.level_Condensed_diagram' :=
{ X := Condensed_Ab_to_CondensedSet.obj (to_Condensed.obj A),
  ι :=
  { app := λ r, Sheaf.hom.mk $
    { app := λ S f, ulift.up $ ⟨_, ulift.down r, f.down.1, f.down.2, rfl⟩,
      naturality' := λ S T f, by { ext, refl } },
    naturality' := λ r s h, by { ext, refl } } } .

def colimit_iso_Condensed_obj :
  colimit A.level_Condensed_diagram' ≅ Condensed_Ab_to_CondensedSet.obj (to_Condensed.obj A) :=
calc
  _ ≅ _ : (colimit.is_colimit _).cocone_point_unique_up_to_iso (filtered_cocone_is_colimit _)
  ... ≅ _ : Sheaf.iso.mk _ (Condensed_Ab_to_CondensedSet.{u}.obj (to_Condensed.{u}.obj A)) $
  nat_iso.of_components (λ X,
    (is_colimit_of_preserves ((evaluation _ _).obj X)
      (colimit.is_colimit (A.level_Condensed_diagram' ⋙
        Sheaf_to_presheaf _ _))).cocone_point_unique_up_to_iso (colimit.is_colimit _) ≪≫
    (colimit.is_colimit _).cocone_point_unique_up_to_iso
    (types.colimit_cocone_is_colimit _) ≪≫
    equiv.to_iso
    { to_fun := quot.lift
        begin
          intros r,
          exact ulift.up ⟨_, ulift.down r.1, _, r.2.down.2, rfl⟩,
        end
        sorry,
      inv_fun := begin
        intros f,
        choose c f1 hf1 hh using f.down.2,
        apply quot.mk, use ulift.up c,
        dsimp [ulift_functor],
        apply ulift.up,
        exact ⟨f1, hf1⟩,
      end,
      left_inv := sorry,
      right_inv := sorry }
  ) sorry

def colimit_to_Condensed_obj :
  colimit A.level_Condensed_diagram' ⟶ Condensed_Ab_to_CondensedSet.obj (to_Condensed.obj A) :=
colimit.desc _ A.level_Condensed_diagram_cone

instance is_iso_colimit_to_Condensed_obj : is_iso A.colimit_to_Condensed_obj :=
begin
  suffices : A.colimit_to_Condensed_obj =
    A.colimit_iso_Condensed_obj.hom, by { rw this, apply_instance },
  sorry
end

end


end CompHausFiltPseuNormGrp

@[simps obj map {fully_applied := ff}]
def CompHausFiltPseuNormGrp₁.to_Condensed :
  CompHausFiltPseuNormGrp₁.{u} ⥤ Condensed.{u} Ab.{u+1} :=
CompHausFiltPseuNormGrp₁.enlarging_functor ⋙ CompHausFiltPseuNormGrp.to_Condensed
