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

def lift {X Y : Profinite} {P : ExtrDisc} (f : X ⟶ Y)
  (hf : function.surjective f) (e : P.val ⟶ Y) : P.val ⟶ X :=
begin
  haveI : epi f := by rwa Profinite.epi_iff_surjective f,
  choose g h using projective.factors e f,
  exact g,
end

@[simp]
lemma lift_lifts {X Y : Profinite} {P : ExtrDisc} (f : X ⟶ Y)
  (hf : function.surjective f) (e : P.val ⟶ Y) :
  lift f hf e ≫ f = e :=
begin
  haveI : epi f := by rwa Profinite.epi_iff_surjective f,
  apply (projective.factors e f).some_spec,
end

instance (X : ExtrDisc) : topological_space X :=
show topological_space X.val, by apply_instance

instance (X : ExtrDisc) : compact_space X :=
show compact_space X.val, by apply_instance

instance (X : ExtrDisc) : t2_space X :=
show t2_space X.val, by apply_instance

instance (X : ExtrDisc) : totally_disconnected_space X :=
show totally_disconnected_space X.val, by apply_instance

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

--instance (Y : Profinite) : t2_space Y := infer_instance

structure presentation (B : Profinite) :=
(G : ExtrDisc)
(π : G.val ⟶ B)
(hπ : function.surjective π)
(R : ExtrDisc)
(r : R.val ⟶ Profinite.pullback π π)
(hr : function.surjective r)

@[simps]
def presentation.fst {B : Profinite} (X : B.presentation) :
  X.R ⟶ X.G := ⟨X.r ≫ pullback.fst _ _⟩

@[simps]
def presentation.snd {B : Profinite} (X : B.presentation) :
  X.R ⟶ X.G := ⟨X.r ≫ pullback.snd _ _⟩

@[simps]
def presentation.map_G {B₁ B₂ : Profinite} (X₁ : B₁.presentation)
  (X₂ : B₂.presentation) (f : B₁ ⟶ B₂) : X₁.G ⟶ X₂.G :=
⟨ExtrDisc.lift X₂.π X₂.hπ (X₁.π ≫ f)⟩

@[simp, reassoc]
lemma presentation.map_G_π {B₁ B₂ : Profinite} (X₁ : B₁.presentation)
  (X₂ : B₂.presentation) (f : B₁ ⟶ B₂) :
  (X₁.map_G X₂ f).val ≫ X₂.π = X₁.π ≫ f :=
begin
  dsimp [presentation.map_G],
  simp,
end

-- this is essentially a truncated simplicial homotopy between `σ₁` and `σ₂`.
@[simps]
def presentation.map_R {B₁ B₂ : Profinite} (X₁ : B₁.presentation)
  (X₂ : B₂.presentation) (f : B₁ ⟶ B₂)
  (σ₁ σ₂ : X₁.G ⟶ X₂.G)
  (w₁ : σ₁.val ≫ X₂.π = X₁.π ≫ f)
  (w₂ : σ₂.val ≫ X₂.π = X₁.π ≫ f) : X₁.R ⟶ X₂.R :=
⟨ExtrDisc.lift _ X₂.hr $ X₁.r ≫ pullback.lift _ _
  (pullback.fst _ _ ≫ σ₁.val)
  (pullback.snd _ _ ≫ σ₂.val)
  (by simp [pullback.condition_assoc, w₁, w₂] )⟩

@[simp, reassoc]
lemma presentation.map_R_fst {B₁ B₂ : Profinite} (X₁ : B₁.presentation)
  (X₂ : B₂.presentation) (f : B₁ ⟶ B₂) (σ₁ σ₂ : X₁.G ⟶ X₂.G)
  (w₁ : σ₁.val ≫ X₂.π = X₁.π ≫ f)
  (w₂ : σ₂.val ≫ X₂.π = X₁.π ≫ f) :
  X₁.map_R X₂ f σ₁ σ₂ w₁ w₂ ≫ X₂.fst = X₁.fst ≫ σ₁ := sorry

@[simp, reassoc]
lemma presentation.map_R_snd {B₁ B₂ : Profinite} (X₁ : B₁.presentation)
  (X₂ : B₂.presentation) (f : B₁ ⟶ B₂) (σ₁ σ₂ : X₁.G ⟶ X₂.G)
  (w₁ : σ₁.val ≫ X₂.π = X₁.π ≫ f)
  (w₂ : σ₂.val ≫ X₂.π = X₁.π ≫ f) :
  X₁.map_R X₂ f σ₁ σ₂ w₁ w₂ ≫ X₂.snd = X₁.snd ≫ σ₂ := sorry

-- Use the free stuff.
lemma exists_presentation (X : Profinite) : ∃ (P : X.presentation), true := sorry

@[irreducible]
def pres (X : Profinite.{u}) : X.presentation :=
X.exists_presentation.some

structure presentation.hom_over {B₁ B₂ : Profinite}
  (X₁ : B₁.presentation) (X₂ : B₂.presentation) (f : B₁ ⟶ B₂) :=
(g : X₁.G ⟶ X₂.G)
(w : ExtrDisc.hom.val g ≫ X₂.π = X₁.π ≫ f)

lemma presentation.exists_lift {B₁ B₂ : Profinite}
  (X₁ : B₁.presentation) (X₂ : B₂.presentation) (f : B₁ ⟶ B₂) :
  ∃ F : X₁.hom_over X₂ f, true := sorry

@[irreducible]
def presentation.lift {B₁ B₂ : Profinite}
  (X₁ : B₁.presentation) (X₂ : B₂.presentation) (f : B₁ ⟶ B₂) :
  X₁.hom_over X₂ f := (X₁.exists_lift X₂ f).some

def presentation.id {B : Profinite} (X : B.presentation) :
  X.hom_over X (𝟙 _) :=
{ g := 𝟙 _,
  w := by simp }

def presentation.hom_over.comp {B₁ B₂ B₃ : Profinite}
  {X₁ : B₁.presentation}
  {X₂ : B₂.presentation}
  {X₃ : B₃.presentation}
  {f₁ : B₁ ⟶ B₂}
  {f₂ : B₂ ⟶ B₃}
  (e₁ : X₁.hom_over X₂ f₁) (e₂ : X₂.hom_over X₃ f₂) : X₁.hom_over X₃ (f₁ ≫ f₂) :=
{ g := e₁.g ≫ e₂.g,
  w := by simp [e₂.w, reassoc_of e₁.w], }

structure presentation.hom_over.relator {B₁ B₂ : Profinite} {X₁ : B₁.presentation}
  {X₂ : B₂.presentation} {f : B₁ ⟶ B₂} (e₁ e₂ : X₁.hom_over X₂ f) :=
(r : X₁.R ⟶ X₂.R)
(fst : r ≫ X₂.fst = X₁.fst ≫ e₁.g)
(snd : r ≫ X₂.snd = X₁.snd ≫ e₁.g)

lemma presentation.hom_over.exists_relator {B₁ B₂ : Profinite} {X₁ : B₁.presentation}
  {X₂ : B₂.presentation} {f : B₁ ⟶ B₂} (e₁ e₂ : X₁.hom_over X₂ f) :
  ∃ (r : e₁.relator e₂), true := sorry

@[irreducible]
def presentation.hom_over.relate {B₁ B₂ : Profinite} {X₁ : B₁.presentation}
  {X₂ : B₂.presentation} {f : B₁ ⟶ B₂} (e₁ e₂ : X₁.hom_over X₂ f) : e₁.relator e₂ :=
(e₁.exists_relator e₂).some

def presentation.terminal : Profinite.empty.presentation :=
{ G := ExtrDisc.empty,
  π := ⟨λ x, pempty.elim x, continuous_bot⟩,
  hπ := by tidy,
  R := ExtrDisc.empty,
  r := ⟨λ x, pempty.elim x, continuous_bot⟩,
  hr := by tidy }

end Profinite

--- Start here...
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

/-
@[simps]
def ExtrDisc.via_pullback_fst {X Y Z : ExtrDisc} (f : Y ⟶ X)
  (g : Z.val ⟶ Profinite.pullback f.val f.val) :
  Z ⟶ Y := ⟨g ≫ Profinite.pullback.fst f.val f.val⟩

@[simps]
def ExtrDisc.via_pullback_snd {X Y Z : ExtrDisc} (f : Y ⟶ X)
  (g : Z.val ⟶ Profinite.pullback f.val f.val) :
  Z ⟶ Y := ⟨g ≫ Profinite.pullback.snd f.val f.val⟩

@[reassoc]
lemma ExtrDisc.via_pullback_condition {X Y Z : ExtrDisc} (f : Y ⟶ X)
  (g : Z.val ⟶ Profinite.pullback f.val f.val) :
  ExtrDisc.via_pullback_fst f g ≫ f = ExtrDisc.via_pullback_snd f g ≫ f :=
begin
  dsimp [ExtrDisc.via_pullback_fst, ExtrDisc.via_pullback_snd],
  ext1,
  dsimp,
  simp [Profinite.pullback.condition],
end
-/

open opposite category_theory.limits

def ExtrSheaf.map_to_equalizer (F : ExtrSheaf.{u} C) {B : ExtrDisc}
  (P : B.val.presentation) : F.val.obj (op B) ⟶
  limits.equalizer (F.val.map P.fst.op) (F.val.map P.snd.op) :=
limits.equalizer.lift (F.val.map (quiver.hom.op ⟨P.π⟩)) $
begin
  simp only [← F.val.map_comp, ← op_comp],
  congr' 2,
  ext1,
  simp [Profinite.pullback.condition],
end

-- This should follow from the projectivity of the objects involved.
lemma ExtrSheaf.equalizer_condition (F : ExtrSheaf.{u} C) {B : ExtrDisc}
  (P : B.val.presentation) :
  is_iso (F.map_to_equalizer P) :=
begin
  --TODO: Add general stuff about split (co)equalizers.
  --This is a fun proof!

  -- First, let's split the surjective `π : P.G ⟶ B`.
  let s : B ⟶ P.G := ⟨ExtrDisc.lift _ P.hπ (𝟙 _)⟩,
  have hs : s ≫ ⟨P.π⟩ = 𝟙 _ := by { ext1, apply ExtrDisc.lift_lifts },

  -- Now, consider the map from `P.G` to the pullback of `P.π` with itself
  -- given by `𝟙 B` on one component and `f ≫ s` on the other.
  let e : P.G.val ⟶ Profinite.pullback P.π P.π :=
    Profinite.pullback.lift _ _ (𝟙 _) (P.π ≫ s.val) _,
  swap,
  { apply_fun (λ e, e.val) at hs, change s.val ≫ P.π = 𝟙 _ at hs, simp [hs] },

  -- Since `g`, the map from `Z` to this pullback, is surjective (hence epic),
  -- we can use the projectivity of `Y` to lift `e` above to a morphism
  -- `t : Y ⟶ Z`.
  -- The universal property ensures that `t` composed with the first projection
  -- is the identity (i.e. `t` splits the map from `Z` to the pullback via `g`),
  -- and `t` composed with the second projection becomes `f ≫ s`.

  -- We have thus obtained the basic setting of a split equalizer,
  -- Once we apply `F` (which is a presheaf), we obtain a split coequalizer.
  -- Now we simply need to use the fact that the cofork point of a split
  -- coequalizer is the coequalizer of the diagram, and the proof below does
  -- essentially this.

  let t : P.G ⟶ P.R := ⟨ExtrDisc.lift _ P.hr e⟩,
  have ht : t.val ≫ P.r = e := by apply ExtrDisc.lift_lifts,

  -- Just some abbreviations for the stuff below.
  let e₁ := F.val.map P.fst.op,
  let e₂ := F.val.map P.snd.op,

  -- This will become the inverse of the canonical map from the cofork point...
  let i : limits.equalizer e₁ e₂ ⟶ F.val.obj (op B) :=
    limits.equalizer.ι e₁ e₂ ≫ F.val.map s.op,

  -- so we use it!
  use i,
  split,
  { -- The first step of the proof follows simply from the fact that `s` splits `f`.
    dsimp [ExtrSheaf.map_to_equalizer, i],
    simp only [limits.equalizer.lift_ι_assoc, ← F.val.map_comp, ← op_comp, hs,
      op_id, F.val.map_id] },
  { -- The rest of the proof uses the properties of `t` mentioned above.
    ext,
    dsimp [i, ExtrSheaf.map_to_equalizer],
    simp only [limits.equalizer.lift_ι, category.id_comp, category.assoc,
      ← F.val.map_comp, ← op_comp],
    let π' : P.G ⟶ B := ⟨P.π⟩,
    have : π' ≫ s = t ≫ P.snd,
    { ext1,
      dsimp [π'],
      rw reassoc_of ht,
      dsimp only [e],
      simp },
    dsimp only [e₁, e₂],
    rw [this, op_comp, F.val.map_comp, ← category.assoc, ← limits.equalizer.condition,
      category.assoc, ← F.val.map_comp, ← op_comp],
    have : t ≫ P.fst = 𝟙 _,
    { ext1,
      dsimp,
      change t.val ≫ _ ≫ _ = 𝟙 _,
      rw reassoc_of ht,
      dsimp [e],
      simp, },
    rw [this, op_id, F.val.map_id, category.comp_id], }
end

-- We now use a totally noncomputable presentation! (This should be generalizable...)
def ExtrSheaf.extend_to_obj (F : ExtrSheaf.{u} C) (X : Profinite.{u}) : C :=
limits.equalizer (F.val.map X.pres.fst.op) (F.val.map X.pres.snd.op)

def ExtrSheaf.extend_to_hom (F : ExtrSheaf.{u} C) {X Y : Profinite.{u}} (f : X ⟶ Y)
  (e : X.pres.hom_over Y.pres f) :
  F.extend_to_obj Y ⟶ F.extend_to_obj X :=
limits.equalizer.lift (limits.equalizer.ι _ _ ≫ F.val.map e.g.op)
begin
  simp only [category.assoc, ← F.val.map_comp, ← op_comp],
  simp only [← (e.relate e).fst, ← (e.relate e).snd, F.val.map_comp,
    op_comp, limits.equalizer.condition_assoc],
end

lemma ExtrSheaf.extend_to_hom_unique (F : ExtrSheaf.{u} C) {X Y : Profinite.{u}} (f : X ⟶ Y)
  (e₁ e₂ : X.pres.hom_over Y.pres f) :
  F.extend_to_hom f e₁ = F.extend_to_hom f e₂ := sorry

@[simps]
def ExtrSheaf.extend_to_presheaf (F : ExtrSheaf.{u} C) : Profiniteᵒᵖ ⥤ C :=
{ obj := λ X, F.extend_to_obj X.unop,
  map := λ X Y f, F.extend_to_hom f.unop $ Y.unop.pres.lift X.unop.pres f.unop,
  map_id' := begin
    intros X,
    erw F.extend_to_hom_unique _ (X.unop.pres.lift X.unop.pres (𝟙 _)) X.unop.pres.id,
    ext1,
    dsimp [ExtrSheaf.extend_to_hom, Profinite.presentation.id],
    simp,
  end,
  map_comp' := begin
    intros X Y Z f g,
    erw F.extend_to_hom_unique _ (Z.unop.pres.lift X.unop.pres (g.unop ≫ f.unop))
      ((Z.unop.pres.lift Y.unop.pres g.unop).comp
        (Y.unop.pres.lift X.unop.pres f.unop)),
    ext1,
    dsimp [ExtrSheaf.extend_to_hom, Profinite.presentation.hom_over.comp],
    simp,
  end }

-- Note for AT:
-- This will be a bit hard... One should use the proetale sheaf condition involving
-- binary products, the empty profinite set, and equalizers.
-- One should presumably also use `ExtrSheaf.equalizer_condition` above.
-- Essentially, this proof is about various limits commuting with other limits.
-- I think it will be easiest to just construct the inverses needed for preserving empty,
-- products and equalizers in terms of `limit.lift` for various kinds of limits.


lemma ExtrSheaf.empty_condition_extend (F : ExtrSheaf.{u} C) :
  F.extend_to_presheaf.empty_condition' :=
begin
  dsimp [functor.empty_condition'],
  have := F.2,
  dsimp [ExtrDisc.terminal_condition] at this,
  resetI,
  let e : F.extend_to_obj Profinite.empty ⟶ F.val.obj (op ExtrDisc.empty) :=
    equalizer.ι _ _ ≫ F.val.map (ExtrDisc.empty.elim _).op,
  haveI : is_iso e := begin
    let i : F.val.obj (op ExtrDisc.empty) ⟶ F.extend_to_obj Profinite.empty :=
      equalizer.lift _ _,
    rotate,
    { apply F.val.map, apply quiver.hom.op,
      use (Profinite.empty.pres.lift Profinite.presentation.terminal (𝟙 _)).g },
    { simp only [← F.val.map_comp, ← op_comp],
      congr' 2,
      let R := (Profinite.empty.pres.lift Profinite.presentation.terminal
          (𝟙 Profinite.empty)).relate
        (Profinite.empty.pres.lift Profinite.presentation.terminal (𝟙 Profinite.empty)),
      rw [← R.fst, ← R.snd],
      congr' 1,
      ext x, cases x },
    use i,
    split,
    { dsimp [i, e],
      ext,
      simp only [equalizer.lift_ι, category.id_comp, category.assoc],
      rw [← F.val.map_comp, ← op_comp],
      convert category.comp_id _ using 2,
      rw [← F.val.map_id, ← op_id],
      congr' 2,
      ext x : 2,
      apply pempty.elim (Profinite.empty.pres.π x) },
    { dsimp [i,e],
      rw [equalizer.lift_ι_assoc, ← F.val.map_comp, ← op_comp, ← F.val.map_id, ← op_id],
      congr' 2,
      ext ⟨x⟩ }
  end,
  suffices : is_iso (inv e ≫ terminal.from (F.extend_to_obj Profinite.empty)),
  { resetI,
    use inv (inv e ≫ terminal.from (F.extend_to_obj Profinite.empty)) ≫ inv e,
    split, { rw [← category.assoc, is_iso.comp_inv_eq], simp, }, { simp } },
  have : inv e ≫ terminal.from (F.extend_to_obj Profinite.empty) =
    terminal.from _, by apply subsingleton.elim,
  rw this,
  apply_instance,
end

lemma ExtrSheaf.product_condition_extend (F : ExtrSheaf.{u} C) :
  F.extend_to_presheaf.product_condition' := sorry

lemma ExtrSheaf.equalizer_condition_extend (F : ExtrSheaf.{u} C) :
  F.extend_to_presheaf.equalizer_condition' := sorry

theorem ExtrSheaf.extend_is_sheaf (F : ExtrSheaf.{u} C) : presheaf.is_sheaf proetale_topology
  F.extend_to_presheaf :=
begin
  rw F.extend_to_presheaf.is_proetale_sheaf_tfae.out 0 3,
  refine ⟨F.empty_condition_extend, F.product_condition_extend,
    F.equalizer_condition_extend⟩,
end

def ExtrSheaf.extend (F : ExtrSheaf.{u} C) : Condensed C :=
⟨F.extend_to_presheaf, F.extend_is_sheaf⟩

/-
def ExtrSheaf.extend_restrict_hom (F : ExtrSheaf.{u} C) :
  F ⟶ (Condensed_to_ExtrSheaf C).obj F.extend := ExtrSheaf.hom.mk $
{ app := λ X, limits.equalizer.lift
    (F.val.map $ eq_to_hom (X.op_unop).symm ≫ quiver.hom.op ⟨X.unop.val.pres_π⟩) begin
      dsimp [Profinite.rels_fst, Profinite.rels_snd, Profinite.free_presentation],
      simp only [← F.val.map_comp, category.id_comp, ← op_comp],
      congr' 2,
      apply ExtrDisc.hom.ext,
      simp [Profinite.pullback.condition],
    end,
  naturality' := begin
    intros A B f,
    ext,
    dsimp [Condensed_to_ExtrSheaf],
    simp only [limits.equalizer.lift_ι, category.id_comp, category.assoc],
    dsimp [ExtrSheaf.extend, ExtrSheaf.extend_to_hom],
    simp only [limits.equalizer.lift_ι, limits.equalizer.lift_ι_assoc],
    simp only [← F.val.map_comp, ← op_comp],
    rw [← f.op_unop, ← op_comp],
    congr' 2,
    apply ExtrDisc.hom.ext,
    exact (Profinite.map_pres_π f.unop.val).symm,
  end }

-- This should follow from the equalizer condition which is proved for `ExtrSheaf` above.
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
{ app := λ X, limits.equalizer.lift (F.val.map X.unop.pres_π.op) begin
    dsimp [Condensed_to_ExtrSheaf],
    simp only [← F.val.map_comp, ← op_comp, category.assoc,
      Profinite.pullback.condition],
  end,
  naturality' := begin
    intros S T f,
    ext,
    dsimp [Condensed_to_ExtrSheaf],
    simp only [limits.equalizer.lift_ι, category.assoc],
    erw [limits.equalizer.lift_ι],
    erw [limits.equalizer.lift_ι_assoc],
    dsimp,
    simp only [← F.val.map_comp, ← op_comp],
    rw Profinite.map_pres_π,
    refl,
  end }

-- This map is an equalizer inclusion, and so is a mono.
lemma Condensed.mono_map_of_surjective (F : Condensed.{u} C) {X Y : Profinite}
  (f : Y ⟶ X) (hf : function.surjective f) : mono (F.val.map f.op) :=
begin
  have := F.2,
  rw F.val.is_proetale_sheaf_tfae.out 0 3 at this,
  obtain ⟨_,_,h⟩ := this,
  let t :=
    F.val.map_to_equalizer' f (Profinite.pullback.fst f f)
      (Profinite.pullback.snd f f) _,
  have : F.val.map f.op = t ≫ limits.equalizer.ι _ _,
  { dsimp [t, functor.map_to_equalizer'],
    simp },
  rw this,
  specialize h _ _ f hf,
  change is_iso t at h,
  resetI,
  have := mono_comp t (limits.equalizer.ι _ _),
  apply this,
end

lemma Condensed.equalizer_condition (F : Condensed.{u} C) {X Y Z : Profinite}
  (f : Y ⟶ X) (hf : function.surjective f) (g : Z ⟶ Profinite.pullback f f)
  (hg : function.surjective g) :
  is_iso (F.val.map_to_equalizer' f (g ≫ Profinite.pullback.fst _ _)
    (g ≫ Profinite.pullback.snd _ _) $ by simp [Profinite.pullback.condition] ) :=
begin
  have := F.2,
  rw F.val.is_proetale_sheaf_tfae.out 0 3 at this,
  obtain ⟨_,_,h⟩ := this,
  specialize h Y X f hf,
  -- TODO: generalize these isomorphisms between various equalizers.
  let E₁ := limits.equalizer
    (F.val.map (Profinite.pullback.fst f f).op)
    (F.val.map (Profinite.pullback.snd f f).op),
  let E₂ := limits.equalizer
    (F.val.map (g ≫ Profinite.pullback.fst f f).op)
    (F.val.map (g ≫ Profinite.pullback.snd f f).op),
  let e : E₁ ⟶ E₂ :=
    limits.equalizer.lift (limits.equalizer.ι _ _) (by simp [limits.equalizer.condition_assoc]),
  haveI : is_iso e := begin
    let i : E₂ ⟶ E₁ :=
      limits.equalizer.lift (limits.equalizer.ι _ _) _,
    swap,
    { haveI : mono (F.val.map g.op) := F.mono_map_of_surjective _ hg,
      rw ← cancel_mono (F.val.map g.op),
      dsimp, simp only [category.assoc, ← F.val.map_comp, ← op_comp],
      apply limits.equalizer.condition },
    use i,
    split,
    { dsimp [i, e], ext, simp },
    { dsimp [i, e], ext, simp, dsimp, simp, },
  end,
  let t := F.val.map_to_equalizer' f
    (g ≫ Profinite.pullback.fst f f)
    (g ≫ Profinite.pullback.snd f f) _,
  swap, { simp [Profinite.pullback.condition] },
  change is_iso t,
  suffices : is_iso (t ≫ inv e),
  { resetI,
    use inv e ≫ inv (t ≫ inv e),
    split,
    { simp only [← category.assoc, is_iso.hom_inv_id] },
    { simp } },
  have : t ≫ inv e =
    F.val.map_to_equalizer' f (Profinite.pullback.fst f f) (Profinite.pullback.snd f f) _,
  { rw is_iso.comp_inv_eq,
    ext,
    dsimp [t, e, functor.map_to_equalizer'],
    simp },
  -- Closes the other goal because proof appears in assumption.
  rwa this,
end

instance restrict_extend_hom_app_is_iso (F : Condensed.{u} C) (X : Profiniteᵒᵖ) :
  is_iso (F.restrict_extend_hom.val.app X) :=
begin
  dsimp [Condensed.restrict_extend_hom],
  have := F.equalizer_condition,
  apply this,
  apply Profinite.pres_π_surjective,
  apply Profinite.pres_π_surjective,
end

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
    (limits.equalizer.ι _ _ ≫ η.val.app _) begin
      simp only [category.assoc, ← η.val.naturality,
        limits.equalizer.condition_assoc],
    end,
  naturality' := begin
    intros S T f,
    dsimp [ExtrSheaf.extend_to_hom],
    ext,
    simp,
  end }

@[simp]
lemma ExtrSheaf.extend_nat_trans_id (F : ExtrSheaf.{u} C) :
  ExtrSheaf.extend_nat_trans (𝟙 F) = 𝟙 _ :=
begin
  ext S,
  dsimp [ExtrSheaf.extend_nat_trans],
  simp,
end

@[simp]
lemma ExtrSheaf.extend_nat_trans_comp {F G H : ExtrSheaf.{u} C} (η : F ⟶ G) (γ : G ⟶ H) :
  ExtrSheaf.extend_nat_trans (η ≫ γ) =
  ExtrSheaf.extend_nat_trans η ≫ ExtrSheaf.extend_nat_trans γ :=
begin
  ext,
  dsimp [ExtrSheaf.extend_nat_trans],
  simp,
end

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
    inv_hom_id' := is_iso.inv_hom_id _ }) begin
      intros X Y f,
      ext,
      dsimp [ExtrSheaf.extend_restrict_hom, ExtrSheaf.extend_nat_trans],
      simp,
    end)
(nat_iso.of_components (λ X,
  { hom := let e := inv X.restrict_extend_hom in e,
    inv := X.restrict_extend_hom,
    hom_inv_id' := is_iso.inv_hom_id _,
    inv_hom_id' := is_iso.hom_inv_id _ }) begin
      intros X Y f,
      dsimp,
      rw [is_iso.comp_inv_eq, category.assoc, is_iso.eq_inv_comp],
      ext,
      dsimp [Condensed.restrict_extend_hom, ExtrSheaf.extend_nat_trans],
      simp,
    end)
-/

end
