import topology.category.Profinite.projective
import for_mathlib.Profinite.disjoint_union
import condensed.is_proetale_sheaf
import condensed.basic

noncomputable theory

@[simp]
lemma ultrafilter_extend_extends_apply {α X : Type*}
  [topological_space X] [t2_space X]
  (f : α → X) (a : α) :
  ultrafilter.extend f (pure a) = f a :=
begin
  change (ultrafilter.extend _ ∘ pure) _ = _,
  rw ultrafilter_extend_extends,
end

open category_theory

universes u w v

structure ExtrDisc :=
(val : Profinite.{u})
[cond : projective val]

namespace ExtrDisc

@[ext]
structure hom (X Y : ExtrDisc) := mk :: (val : X.val ⟶ Y.val)

def of (X : Profinite) [projective X] : ExtrDisc := ⟨X⟩

@[simp]
def of_val (X : Profinite) [projective X] : (of X).val = X := rfl

@[simps]
instance : category ExtrDisc :=
{ hom := hom,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val⟩ }

@[simps]
def _root_.ExtrDisc_to_Profinite : ExtrDisc ⥤ Profinite :=
{ obj := val,
  map := λ X Y f, f.val }

instance : concrete_category ExtrDisc.{u} :=
{ forget := ExtrDisc_to_Profinite ⋙ forget _,
  forget_faithful := ⟨⟩ }

instance : has_coe_to_sort ExtrDisc Type* :=
concrete_category.has_coe_to_sort _

instance {X Y : ExtrDisc} : has_coe_to_fun (X ⟶ Y) (λ f, X → Y) :=
⟨λ f, f.val⟩

instance (X : ExtrDisc) : projective X.val := X.cond

example (X : ExtrDisc) : projective (ExtrDisc_to_Profinite.obj X) :=
by { dsimp, apply_instance }

def split {X Y : ExtrDisc} (f : X ⟶ Y) (hf : function.surjective f) :
  Y ⟶ X :=
begin
  have : epi f.val, by  rwa Profinite.epi_iff_surjective f.val,
  resetI,
  choose g h using projective.factors (𝟙 Y.val) f.val,
  exact ⟨g⟩,
end

@[simp, reassoc]
lemma splitting_is_splitting {X Y : ExtrDisc} (f : X ⟶ Y)
  (hf : function.surjective f) : split f hf ≫ f = 𝟙 _ :=
begin
  have : epi f.val, by  rwa Profinite.epi_iff_surjective f.val,
  resetI,
  ext1,
  exact (projective.factors (𝟙 Y.val) f.val).some_spec,
end

instance (X : ExtrDisc) : topological_space X :=
show topological_space X.val, by apply_instance

instance (X : ExtrDisc) : compact_space X :=
show compact_space X.val, by apply_instance

instance (X : ExtrDisc) : t2_space X :=
show t2_space X.val, by apply_instance

instance (X : ExtrDisc) : totally_disconnected_space X :=
show totally_disconnected_space X.val, by apply_instance

def free (α : Type u) : ExtrDisc.{u} :=
{ val := Profinite.of $ ultrafilter α,
  cond := Profinite.projective_ultrafilter α }

def free.ι (α : Type u) : α → free α :=
λ t, (pure t : ultrafilter α)

@[simp]
lemma free.ι_apply {α : Type u} (a : α) : free.ι α a = (pure a : ultrafilter α) := rfl

def free.lift {X : ExtrDisc.{u}} {α : Type u} (f : α → X) : free α ⟶ X :=
⟨⟨ultrafilter.extend f, continuous_ultrafilter_extend _⟩⟩

@[simp]
lemma free.lift_apply {X : ExtrDisc.{u}} {α : Type u} (f : α → X) (F : free α) :
  free.lift f F = ultrafilter.extend f F := rfl

@[simp]
lemma free.ι_lift {X : ExtrDisc.{u}} {α : Type u} (f : α → X) :
  free.lift f ∘ free.ι _ = f :=
begin
  ext,
  dsimp,
  simp,
end

@[simp]
lemma free.ι_lift_apply {X : ExtrDisc.{u}} {α : Type u} (f : α → X) (a : α) :
  free.lift f (free.ι α a) = f a :=
show (free.lift f ∘ free.ι α) a = f a, by simp

lemma free.lift_unique {X : ExtrDisc.{u}} {α : Type u} (f : α → X)
  (g : free α ⟶ X) (h : g ∘ free.ι α = f) : g = free.lift f :=
begin
  letI hh : topological_space α := ⊥,
  have : dense_range (free.ι α) := dense_range_pure,
  rw ← free.ι_lift f at h,
  ext : 2,
  have := this.equalizer _ _ h,
  erw this,
  refl,
  exact g.val.continuous,
  exact (free.lift f).val.continuous,
end

@[ext]
lemma free.hom_ext {X : ExtrDisc.{u}} {α : Type u} (f g : free α ⟶ X)
  (h : f ∘ (free.ι α) = g ∘ (free.ι α)) : f = g :=
by rw [free.lift_unique _ f rfl, free.lift_unique _ g rfl, h]

@[simps]
def free_functor : Type u ⥤ ExtrDisc.{u} :=
{ obj := λ α, free α,
  map := λ α β f, free.lift $ (free.ι _) ∘ f,
  map_id' := by tidy,
  map_comp' := begin
    intros α β γ f g,
    ext : 2,
    dsimp,
    simp,
  end } .

@[simps]
def adjunction : free_functor ⊣ forget _ :=
adjunction.mk_of_hom_equiv $
{ hom_equiv := λ α X,
  { to_fun := λ f, f ∘ free.ι _,
    inv_fun := λ f, free.lift f,
    left_inv := λ f, by { ext, dsimp, simp },
    right_inv := λ f, by { ext, dsimp, simp } },
  hom_equiv_naturality_left_symm' := λ _ _ _ _ _, by { ext, dsimp, simp },
  hom_equiv_naturality_right' := λ _ _ _ _ _, by { ext, dsimp, simp } } .

@[simps]
def sigma {ι : Type u} [fintype ι] (X : ι → ExtrDisc) : ExtrDisc :=
{ val := Profinite.sigma $ λ i : ι, (X i).val,
  cond := begin
    let Z := Profinite.sigma (λ i : ι, (X i).val),
    let e : Z ≅ ∐ (λ i, (X i).val) :=
      (Profinite.sigma_cofan_is_colimit _).cocone_point_unique_up_to_iso
      (limits.colimit.is_colimit _),
    apply projective.of_iso e.symm,
    apply_instance,
  end }

@[simps]
def sigma.ι {ι : Type u} [fintype ι] (X : ι → ExtrDisc) (i : ι) :
  X i ⟶ sigma X := ⟨Profinite.sigma.ι _ i⟩

@[simps]
def sigma.desc {Y : ExtrDisc} {ι : Type u} [fintype ι] (X : ι → ExtrDisc)
  (f : Π i, X i ⟶ Y) : sigma X ⟶ Y := ⟨Profinite.sigma.desc _ $ λ i, (f i).val⟩

@[simp, reassoc]
lemma sigma.ι_desc {Y} {ι : Type u} (i : ι) [fintype ι] (X : ι → ExtrDisc) (f : Π a, X a ⟶ Y) :
  sigma.ι X i ≫ sigma.desc X f = f _ := by { ext1, simp }

@[ext]
lemma sigma.hom_ext {Y} {ι : Type u} [fintype ι] (X : ι → ExtrDisc) (f g : sigma X ⟶ Y)
  (w : ∀ i, sigma.ι X i ≫ f = sigma.ι X i ≫ g) : f = g :=
begin
  ext1,
  apply Profinite.sigma.hom_ext,
  intros i,
  specialize w i,
  apply_fun (λ e, e.val) at w,
  exact w,
end

def sigma.cofan {ι : Type u} [fintype ι] (X : ι → ExtrDisc) : limits.cofan X :=
limits.cofan.mk (sigma X) $ λ i, sigma.ι _ i

@[simps]
def sigma.is_colimit {ι : Type u} [fintype ι] (X : ι → ExtrDisc) :
  limits.is_colimit (sigma.cofan X) :=
{ desc := λ S, sigma.desc _ $ λ i, S.ι.app i,
  fac' := λ S i, sigma.ι_desc _ _ _,
  uniq' := begin
    intros S m h,
    apply sigma.hom_ext,
    intros i,
    simpa using h i,
  end }

.-- move this
-- @[simps]
def _root_.Profinite.sum_iso_coprod (X Y : Profinite.{u}) :
  Profinite.sum X Y ≅ X ⨿ Y :=
{ hom := Profinite.sum.desc _ _ limits.coprod.inl limits.coprod.inr,
  inv := limits.coprod.desc (Profinite.sum.inl _ _) (Profinite.sum.inr _ _),
  hom_inv_id' := by { apply Profinite.sum.hom_ext;
    simp only [← category.assoc, category.comp_id, Profinite.sum.inl_desc,
      limits.coprod.inl_desc, Profinite.sum.inr_desc, limits.coprod.inr_desc] },
  inv_hom_id' := by { apply limits.coprod.hom_ext;
    simp only [← category.assoc, category.comp_id, Profinite.sum.inl_desc,
      limits.coprod.inl_desc, Profinite.sum.inr_desc, limits.coprod.inr_desc] } }

@[simps]
def sum (X Y : ExtrDisc.{u}) : ExtrDisc.{u} :=
{ val := Profinite.sum X.val Y.val,
  cond := begin
    let Z := Profinite.sum X.val Y.val,
    apply projective.of_iso (Profinite.sum_iso_coprod X.val Y.val).symm,
    apply_instance,
  end }

@[simps]
def sum.inl (X Y : ExtrDisc) : X ⟶ sum X Y :=
⟨Profinite.sum.inl _ _⟩

@[simps]
def sum.inr (X Y : ExtrDisc) : Y ⟶ sum X Y :=
⟨Profinite.sum.inr _ _⟩

@[simps]
def sum.desc {X Y Z : ExtrDisc} (f : X ⟶ Z) (g : Y ⟶ Z) :
  sum X Y ⟶ Z :=
⟨Profinite.sum.desc _ _ f.val g.val⟩

@[simp]
lemma sum.inl_desc {X Y Z : ExtrDisc} (f : X ⟶ Z) (g : Y ⟶ Z) :
  sum.inl X Y ≫ sum.desc f g = f :=
by { ext1, dsimp, simp }

@[simp]
lemma sum.inr_desc {X Y Z : ExtrDisc} (f : X ⟶ Z) (g : Y ⟶ Z) :
  sum.inr X Y ≫ sum.desc f g = g :=
by { ext1, dsimp, simp }

@[ext]
lemma sum.hom_ext {X Y Z : ExtrDisc} (f g : sum X Y ⟶ Z)
  (hl : sum.inl X Y ≫ f = sum.inl X Y ≫ g)
  (hr : sum.inr X Y ≫ f = sum.inr X Y ≫ g) : f = g :=
begin
  ext1,
  apply Profinite.sum.hom_ext,
  { apply_fun (λ e, e.val) at hl, exact hl },
  { apply_fun (λ e, e.val) at hr, exact hr }
end

-- move this
lemma _root_.Profinite.empty_is_initial : limits.is_initial Profinite.empty.{u} :=
@limits.is_initial.of_unique.{u} _ _ _ (λ Y, ⟨⟨Profinite.empty.elim _⟩, λ f, by { ext, cases x, }⟩)

@[simps]
def empty : ExtrDisc :=
{ val := Profinite.empty,
  cond := begin
    let e : Profinite.empty ≅ ⊥_ _ :=
    Profinite.empty_is_initial.unique_up_to_iso limits.initial_is_initial,
    apply projective.of_iso e.symm,
    -- apply_instance, <-- missing instance : projective (⊥_ _)
    constructor,
    introsI A B f g _,
    refine ⟨limits.initial.to A, by simp⟩,
  end }

@[simps]
def empty.elim (X : ExtrDisc) : empty ⟶ X :=
⟨Profinite.empty.elim _⟩

@[ext]
def empty.hom_ext {X : ExtrDisc} (f g : empty ⟶ X) : f = g :=
by { ext x, cases x }

open opposite

variables {C : Type v} [category.{w} C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C)

def terminal_condition [limits.has_terminal C] : Prop :=
  is_iso (limits.terminal.from (F.obj (op empty)))

def binary_product_condition [limits.has_binary_products C] : Prop := ∀ (X Y : ExtrDisc.{u}),
  is_iso (limits.prod.lift (F.map (sum.inl X Y).op) (F.map (sum.inr X Y).op))

end ExtrDisc

namespace Profinite

instance (Y : Profinite) : t2_space Y := infer_instance

def pres (X : Profinite.{u}) : ExtrDisc.{u} :=
ExtrDisc.free X

def pres_π (X : Profinite.{u}) :
  X.pres.val ⟶ X :=
⟨ultrafilter.extend id, continuous_ultrafilter_extend _⟩

def map_pres {X Y : Profinite.{u}} (f : X ⟶ Y) : X.pres ⟶ Y.pres :=
ExtrDisc.free_functor.map f

-- functoriality of the presentation
@[simp]
lemma map_pres_π {X Y : Profinite.{u}} (f : X ⟶ Y) :
  (map_pres f).val ≫ Y.pres_π = X.pres_π ≫ f :=
begin
  apply_fun (λ e, (forget Profinite).map e),
  swap, { exact (forget Profinite).map_injective },
  dsimp [pres_π, map_pres, ExtrDisc.free.lift, ExtrDisc.free.ι],
  have : dense_range (ExtrDisc.free.ι _ : X → X.pres) := dense_range_pure,
  refine this.equalizer _ _ _,
  continuity,
  exact continuous_ultrafilter_extend id,
  apply continuous_ultrafilter_extend,
  exact continuous_ultrafilter_extend id,
  ext,
  dsimp,
  simp,
end

def rels (X : Profinite.{u}) : ExtrDisc.{u} :=
(Profinite.pullback X.pres_π X.pres_π).pres

def rels_fst (X : Profinite.{u}) : X.rels ⟶ X.pres :=
⟨pres_π _ ≫ Profinite.pullback.fst _ _⟩

def rels_snd (X : Profinite.{u}) : X.rels ⟶ X.pres :=
⟨pres_π _ ≫ Profinite.pullback.snd _ _⟩

def map_rels {X Y : Profinite.{u}} (f : X ⟶ Y) : X.rels ⟶ Y.rels :=
map_pres $ pullback.lift _ _
  (pullback.fst _ _ ≫ (map_pres f).val)
  (pullback.snd _ _ ≫ (map_pres f).val) sorry

lemma rels_fst_map {X Y : Profinite.{u}} (f : X ⟶ Y) :
  X.rels_fst ≫ map_pres f = map_rels f ≫ Y.rels_fst := sorry

lemma rels_snd_map {X Y : Profinite.{u}} (f : X ⟶ Y) :
  X.rels_snd ≫ map_pres f = map_rels f ≫ Y.rels_snd := sorry

/-

Given `X : Profinite`, this is the diagram

β(βX ×_X βX) ⇉ βX

whose colimit is isomorphic to `X`, except here we consider it as a diagram in `ExtrDisc`.

Notation: `βX` = the Stone Cech compactification of `X^δ` (= the set `X` as a discrete space).

-/
def extr_diagram (X : Profinite) : limits.walking_parallel_pair.{u} ⥤ ExtrDisc.{u} :=
limits.parallel_pair X.rels_fst X.rels_snd

end Profinite

section

variables (C : Type v) [category.{w} C] [limits.has_terminal C] [limits.has_binary_products C]

structure ExtrSheaf :=
(val : ExtrDisc.{u}ᵒᵖ ⥤ C)
(terminal : ExtrDisc.terminal_condition val)
(binary_product : ExtrDisc.binary_product_condition val)

namespace ExtrSheaf

variable {C}

@[ext] structure hom (X Y : ExtrSheaf C) := mk :: (val : X.val ⟶ Y.val)

@[simps]
instance : category (ExtrSheaf C) :=
{ hom := hom,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ A B C f g, ⟨f.val ≫ g.val⟩,
  id_comp' := λ X Y η, by { ext1, simp },
  comp_id' := λ X Y γ, by { ext1, simp },
  assoc' := λ X Y Z W a b c, by { ext1, simp } }

end ExtrSheaf

@[simps]
def ExtrSheaf_to_presheaf : ExtrSheaf C ⥤ ExtrDiscᵒᵖ ⥤ C :=
{ obj := λ X, X.val,
  map := λ X Y f, f.val }

instance : full (ExtrSheaf_to_presheaf C) := ⟨λ _ _ f, ⟨f⟩, λ X Y f, by { ext1, refl }⟩
instance : faithful (ExtrSheaf_to_presheaf C) := ⟨⟩

variable [limits.has_equalizers C]

@[simps]
def Condensed_to_ExtrSheaf : Condensed C ⥤ ExtrSheaf C :=
{ obj := λ F,
  { val := ExtrDisc_to_Profinite.op ⋙ F.val,
    terminal := begin
      have hF := F.cond,
      rw (functor.is_proetale_sheaf_tfae F.val).out 0 3 at hF,
      exact hF.1,
    end,
    binary_product := begin
      have hF := F.cond,
      rw (functor.is_proetale_sheaf_tfae F.val).out 0 3 at hF,
      rcases hF with ⟨h1,h2,h3⟩,
      intros X Y,
      apply h2,
    end },
  map := λ F G η, ⟨ whisker_left _ η.val ⟩ }

variable {C}

def ExtrSheaf.extend_to_obj (F : ExtrSheaf.{u} C) (X : Profinite.{u}) : C :=
limits.equalizer (F.val.map X.rels_fst.op) (F.val.map X.rels_snd.op)

def ExtrSheaf.extend_to_hom (F : ExtrSheaf.{u} C) {X Y : Profinite.{u}} (f : X ⟶ Y) :
  F.extend_to_obj Y ⟶ F.extend_to_obj X :=
limits.equalizer.lift (limits.equalizer.ι _ _ ≫ F.val.map (Profinite.map_pres f).op)
begin
  simp only [category.assoc, ← F.val.map_comp, ← op_comp],
  have := limits.equalizer.condition (F.val.map Y.rels_fst.op) (F.val.map Y.rels_snd.op),
  simp only [Profinite.rels_fst_map, Profinite.rels_snd_map, op_comp, F.val.map_comp,
    ← category.assoc, this],
end

def ExtrSheaf.extend_to_presheaf (F : ExtrSheaf.{u} C) : Profiniteᵒᵖ ⥤ C :=
{ obj := λ X, F.extend_to_obj X.unop,
  map := λ X Y f, F.extend_to_hom f.unop,
  map_id' := sorry,
  map_comp' := sorry }

-- This will be a bit hard... One should use the proetale sheaf condition involving
-- binary products, the empty profinite set, and equalizers.
theorem ExtrSheaf.extend_is_sheaf (F : ExtrSheaf.{u} C) : presheaf.is_sheaf proetale_topology
  F.extend_to_presheaf := sorry

def ExtrSheaf.extend (F : ExtrSheaf.{u} C) : Condensed C :=
⟨F.extend_to_presheaf, F.extend_is_sheaf⟩

def ExtrSheaf.extend_restrict_hom (F : ExtrSheaf.{u} C) :
  F ⟶ (Condensed_to_ExtrSheaf C).obj F.extend := ExtrSheaf.hom.mk $
{ app := λ X, limits.equalizer.lift
    (F.val.map $ eq_to_hom (X.op_unop).symm ≫ quiver.hom.op ⟨X.unop.val.pres_π⟩) sorry,
  naturality' := sorry }

instance extend_restrict_hom_app_is_iso (F : ExtrSheaf.{u} C) (X : ExtrDiscᵒᵖ) :
  is_iso (F.extend_restrict_hom.val.app X) := sorry

instance extend_restrict_hom (F : ExtrSheaf.{u} C) : is_iso F.extend_restrict_hom :=
begin
  haveI : is_iso F.extend_restrict_hom.val := nat_iso.is_iso_of_is_iso_app _,
  use ⟨inv F.extend_restrict_hom.val⟩,
  split,
  all_goals { ext1, dsimp, simp }
end

def Condensed.restrict_extend_hom (F : Condensed.{u} C) :
  F ⟶ ((Condensed_to_ExtrSheaf C).obj F).extend := Sheaf.hom.mk $
{ app := λ X, limits.equalizer.lift (F.val.map X.unop.pres_π.op) sorry,
  naturality' := sorry }

instance restrict_extend_hom_app_is_iso (F : Condensed.{u} C) (X : Profiniteᵒᵖ) :
  is_iso (F.restrict_extend_hom.val.app X) := sorry

instance restrict_extend_hom_is_iso (F : Condensed.{u} C) :
  is_iso F.restrict_extend_hom :=
begin
  haveI : is_iso F.restrict_extend_hom.val := nat_iso.is_iso_of_is_iso_app _,
  use ⟨inv F.restrict_extend_hom.val⟩,
  split,
  all_goals { ext1, dsimp, simp }
end

def ExtrSheaf.extend_nat_trans {F G : ExtrSheaf.{u} C} (η : F ⟶ G) :
  F.extend_to_presheaf ⟶ G.extend_to_presheaf :=
{ app := λ X, limits.equalizer.lift
    (limits.equalizer.ι _ _ ≫ η.val.app _) sorry,
  naturality' := sorry }

@[simp]
lemma ExtrSheaf.extend_nat_trans_id (F : ExtrSheaf.{u} C) :
  ExtrSheaf.extend_nat_trans (𝟙 F) = 𝟙 _ := sorry

@[simp]
lemma ExtrSheaf.extend_nat_trans_comp {F G H : ExtrSheaf.{u} C} (η : F ⟶ G) (γ : G ⟶ H) :
  ExtrSheaf.extend_nat_trans (η ≫ γ) =
  ExtrSheaf.extend_nat_trans η ≫ ExtrSheaf.extend_nat_trans γ := sorry

variable (C)
@[simps]
def ExtrSheaf_to_Condensed : ExtrSheaf.{u} C ⥤ Condensed.{u} C :=
{ obj := λ F, F.extend,
  map := λ F G η, ⟨ExtrSheaf.extend_nat_trans η⟩,
  map_id' := λ X, by { ext1, apply ExtrSheaf.extend_nat_trans_id },
  map_comp' := λ X Y Z f g, by { ext1, apply ExtrSheaf.extend_nat_trans_comp } }

def ExtrSheaf_Condensed_equivalence : ExtrSheaf.{u} C ≌ Condensed.{u} C :=
equivalence.mk (ExtrSheaf_to_Condensed C) (Condensed_to_ExtrSheaf C)
(nat_iso.of_components (λ X,
  { hom := X.extend_restrict_hom,
    inv := let e := inv X.extend_restrict_hom in e,
    hom_inv_id' := is_iso.hom_inv_id _,
    inv_hom_id' := is_iso.inv_hom_id _ }) sorry)
(nat_iso.of_components (λ X,
  { hom := let e := inv X.restrict_extend_hom in e,
    inv := X.restrict_extend_hom,
    hom_inv_id' := is_iso.inv_hom_id _,
    inv_hom_id' := is_iso.hom_inv_id _ }) sorry)

end
