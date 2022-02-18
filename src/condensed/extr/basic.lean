import topology.category.Profinite.projective
import for_mathlib.Profinite.disjoint_union
import for_mathlib.concrete_equalizer

noncomputable theory

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
lemma of_val (X : Profinite) [projective X] : (of X).val = X := rfl

@[simps]
instance : category ExtrDisc :=
{ hom := hom,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val⟩ }

@[simps]
def _root_.ExtrDisc_to_Profinite : ExtrDisc ⥤ Profinite :=
{ obj := val,
  map := λ X Y f, f.val }

instance : full ExtrDisc_to_Profinite := { preimage := λ X Y f, ⟨f⟩ }

instance : faithful ExtrDisc_to_Profinite := { }

instance : concrete_category ExtrDisc.{u} :=
{ forget := ExtrDisc_to_Profinite ⋙ forget _,
  forget_faithful := ⟨⟩ }

instance : has_coe_to_sort ExtrDisc Type* :=
concrete_category.has_coe_to_sort _

instance {X Y : ExtrDisc} : has_coe_to_fun (X ⟶ Y) (λ f, X → Y) :=
⟨λ f, f.val⟩

@[simp]
lemma coe_fun_eq {X Y : ExtrDisc} (f : X ⟶ Y) (x : X) :
  f x = f.val x := rfl

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

@[simp, reassoc]
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
def _root_.Profinite.empty_is_initial : limits.is_initial Profinite.empty.{u} :=
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
lemma empty.hom_ext {X : ExtrDisc} (f g : empty ⟶ X) : f = g :=
by { ext x, cases x }

def sigma {ι : Type u} [fintype ι] (X : ι → ExtrDisc) : ExtrDisc :=
{ val := Profinite.sigma $ λ i, (X i).val,
  cond := begin
    let e : Profinite.sigma (λ i, (X i).val) ≅ ∐ (λ i, (X i).val) :=
      (Profinite.sigma_cofan_is_colimit _).cocone_point_unique_up_to_iso
      (limits.colimit.is_colimit _),
    apply projective.of_iso e.symm,
    apply_instance,
  end }

def sigma.ι {ι : Type u} [fintype ι] (X : ι → ExtrDisc) (i) :
  X i ⟶ sigma X := ⟨Profinite.sigma.ι _ i⟩

def sigma.desc {ι : Type u} {Y : ExtrDisc} [fintype ι] (X : ι → ExtrDisc)
  (f : Π i, X i ⟶ Y) : sigma X ⟶ Y := ⟨Profinite.sigma.desc _ $ λ i, (f i).val⟩

lemma sigma.ι_desc {ι : Type u} {Y : ExtrDisc} [fintype ι] (X : ι → ExtrDisc)
  (f : Π i, X i ⟶ Y) (i) : sigma.ι X i ≫ sigma.desc X f = f i :=
begin
  ext1,
  apply Profinite.sigma.ι_desc,
end

lemma sigma.hom_ext {ι : Type u} {Y : ExtrDisc} [fintype ι] (X : ι → ExtrDisc)
  (a b : sigma X ⟶ Y) (w : ∀ i, sigma.ι X i ≫ a = sigma.ι X i ≫ b) : a = b :=
begin
  ext1,
  apply Profinite.sigma.hom_ext,
  intros i,
  specialize w i,
  apply_fun (λ e, e.val) at w,
  exact w,
end

lemma sigma.ι_jointly_surjective {ι : Type u} [fintype ι] (X : ι → ExtrDisc)
  (x : sigma X) : ∃ i (t : X i), sigma.ι X i t = x :=
Profinite.sigma.ι_jointly_surjective _ _

open opposite

variables {C : Type v} [category.{w} C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C)

def terminal_condition [limits.has_terminal C] : Prop :=
  is_iso (limits.terminal.from (F.obj (op empty)))

def binary_product_condition [limits.has_binary_products C] : Prop := ∀ (X Y : ExtrDisc.{u}),
  is_iso (limits.prod.lift (F.map (sum.inl X Y).op) (F.map (sum.inr X Y).op))

def finite_product_condition [limits.has_finite_products C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C) :
  Prop := ∀ (ι : Type u) [fintype ι] (X : ι → ExtrDisc),
begin
  -- Lean is being annoying here...
  resetI,
  let t : Π i, F.obj (op (sigma X)) ⟶ F.obj (op (X i)) := λ i, F.map (sigma.ι X i).op,
  exact is_iso (limits.pi.lift t)
end

def finite_product_condition_for_types (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (ι : Type u) [fintype ι] (X : ι → ExtrDisc),
begin
  resetI,
  dsimp_result {
    let t : Π i, F.obj (op (sigma X)) → F.obj (op (X i)) := λ i, F.map (sigma.ι X i).op,
    let tt : F.obj (op (sigma X)) → Π i, F.obj (op (X i)) := λ x i, t i x,
    exact function.bijective tt }
end

def equalizer_condition [limits.has_equalizers C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C) : Prop :=
  ∀ {R X B : ExtrDisc} (f : X ⟶ B) (hf : function.surjective f)
    (g : R.val ⟶ Profinite.pullback f.val f.val) (hg : function.surjective g),
  let e₁ : R ⟶ X := ⟨g ≫ Profinite.pullback.fst _ _⟩,
      e₂ : R ⟶ X := ⟨g ≫ Profinite.pullback.snd _ _⟩,
      w : e₁ ≫ f = e₂ ≫ f := by { ext1, dsimp [e₁, e₂], simp [Profinite.pullback.condition] },
      h : F.map f.op ≫ F.map e₁.op = F.map f.op ≫ F.map e₂.op :=
        by { simp only [← F.map_comp, ← op_comp, w] } in
  is_iso (limits.equalizer.lift _ h)

def equalizer_condition_for_types (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) : Prop :=
  ∀ {R X B : ExtrDisc} (f : X ⟶ B) (hf : function.surjective f)
    (g : R.val ⟶ Profinite.pullback f.val f.val) (hg : function.surjective g),
  by dsimp_result { exact
  let e₁ : R ⟶ X := ⟨g ≫ Profinite.pullback.fst _ _⟩,
      e₂ : R ⟶ X := ⟨g ≫ Profinite.pullback.snd _ _⟩,
      w : e₁ ≫ f = e₂ ≫ f := by { ext1, dsimp [e₁, e₂], simp [Profinite.pullback.condition] },
      h : F.map f.op ≫ F.map e₁.op = F.map f.op ≫ F.map e₂.op :=
        by { simp only [← F.map_comp, ← op_comp, w] },
      E := { x : F.obj (op X) // F.map e₁.op x = F.map e₂.op x },
      t : F.obj (op B) → E := λ x, ⟨F.map f.op x, begin
        change (F.map f.op ≫ F.map e₁.op) x = (F.map f.op ≫ F.map e₂.op) x,
        rw h,
      end⟩ in
    function.bijective t }

lemma equalizer_condition_holds [limits.has_equalizers C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C) :
  equalizer_condition F :=
begin
  intros R X B f hf g hg,
  dsimp,
  let e₁ : R ⟶ X := ⟨g ≫ Profinite.pullback.fst _ _⟩,
  let e₂ : R ⟶ X := ⟨g ≫ Profinite.pullback.snd _ _⟩,
  let σ : B ⟶ X := ⟨ExtrDisc.lift _ hf (𝟙 _)⟩,
  let t : X ⟶ R := ⟨ExtrDisc.lift _ hg _⟩,
  swap,
  { refine Profinite.pullback.lift _ _ (𝟙 _) (f.val ≫ σ.val) _,
    dsimp, simp },
  have h₁ : t ≫ e₁ = 𝟙 _, by { ext1, dsimp, simp },
  have h₂ : t ≫ e₂ = f ≫ σ, by { ext1, dsimp, simp, },
  have hh : σ ≫ f = 𝟙 _, by { ext1, dsimp, simp },
  use (limits.equalizer.ι _ _ ≫ F.map σ.op),
  split,
  { simp only [limits.equalizer.lift_ι_assoc],
    simp only [← F.map_comp, ← op_comp, hh],
    simp },
  { ext,
    simp only [limits.equalizer.lift_ι, category.id_comp, category.assoc],
    simp only [← F.map_comp, ← op_comp],
    erw [← h₂, op_comp, F.map_comp],
    dsimp [e₂],
    erw ← limits.equalizer.condition_assoc,
    change _ ≫ F.map e₁.op ≫ F.map t.op = _,
    rw [← F.map_comp, ← op_comp, h₁],
    simp }
end

lemma equalizer_condition_for_types_holds (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) :
  equalizer_condition_for_types F :=
begin
  -- Should be fairly easy, just mimic the proof in the general case above.
   intros R X B f hf g hg,
  let e₁ : R ⟶ X := ⟨g ≫ Profinite.pullback.fst _ _⟩,
  let e₂ : R ⟶ X := ⟨g ≫ Profinite.pullback.snd _ _⟩,
  have w : e₁ ≫ f = e₂ ≫ f := begin
    dsimp [e₁,e₂],
    apply ExtrDisc.hom.ext,
    simp [category.assoc, Profinite.pullback.condition],
  end,
  have h : F.map f.op ≫ F.map e₁.op = F.map f.op ≫ F.map e₂.op :=
  by { simp only [← F.map_comp, ← op_comp, w] },
  let E := { x : F.obj (op X) // F.map e₁.op x = F.map e₂.op x },
  let t : F.obj (op B) → E := λ x, ⟨F.map f.op x, begin
    change (F.map f.op ≫ F.map e₁.op) x = (F.map f.op ≫ F.map e₂.op) x,
    rw h,
  end⟩,
  change function.bijective t,
  let ee := limits.concrete.equalizer_equiv (F.map e₁.op) (F.map e₂.op),
  suffices : function.bijective (ee.symm ∘ t),
    by exact (equiv.comp_bijective t (equiv.symm ee)).mp this,
  have : ee.symm ∘ t = limits.equalizer.lift _ h,
  { suffices : t = ee ∘ limits.equalizer.lift _ h,
    { rw this, ext, simp, },
    ext,
    apply subtype.ext,
    change _ = (limits.equalizer.lift _ h ≫ limits.equalizer.ι _ _) _,
    rw limits.equalizer.lift_ι,
    refl },
  rw this,
  rw ← is_iso_iff_bijective,
  apply equalizer_condition_holds,
  assumption'
end

end ExtrDisc

namespace Profinite

lemma exists_projective_presentation (B : Profinite.{u}) :
  ∃ (X : ExtrDisc) (π : X.val ⟶ B), function.surjective π :=
begin
  obtain ⟨⟨X,h,π,hπ⟩⟩ := enough_projectives.presentation B,
  resetI,
  use [⟨X⟩, π],
  rwa ← epi_iff_surjective
end

def pres (B : Profinite.{u}) : ExtrDisc :=
  B.exists_projective_presentation.some

def pres_π (B : Profinite.{u}) : B.pres.val ⟶ B :=
  B.exists_projective_presentation.some_spec.some

lemma pres_π_surjective (B : Profinite.{u}) :
  function.surjective B.pres_π :=
B.exists_projective_presentation.some_spec.some_spec

end Profinite

open opposite

variables {C : Type v} [category.{w} C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C)

def is_ExtrSheaf_of_types (P : ExtrDisc.{u}ᵒᵖ ⥤ Type w) : Prop :=
∀ (B : ExtrDisc.{u}) (ι : Type u) [fintype ι] (α : ι → ExtrDisc.{u})
  (f : Π i, α i ⟶ B) (hf : ∀ b : B, ∃ i (x : α i), f i x = b)
  (x : Π i, P.obj (op (α i)))
  (hx : ∀ (i j : ι) (Z : ExtrDisc) (g₁ : Z ⟶ α i) (g₂ : Z ⟶ α j),
    g₁ ≫ f _ = g₂ ≫ f _ → P.map g₁.op (x _) = P.map g₂.op (x _)),
∃! t : P.obj (op B), ∀ i, P.map (f i).op t = x _

-- We encode the general condition essentially using Yoneda.
def is_ExtrSheaf (P : ExtrDisc.{u}ᵒᵖ ⥤ C) : Prop :=
∀ (B : ExtrDisc.{u}) (ι : Type u) [fintype ι] (α : ι → ExtrDisc.{u})
  (f : Π i, α i ⟶ B) (hf : ∀ b : B, ∃ i (x : α i), f i x = b)
  (T : C) (x : Π i, T ⟶ P.obj (op (α i)))
  (hx : ∀ (i j : ι) (Z : ExtrDisc) (g₁ : Z ⟶ α i) (g₂ : Z ⟶ α j),
    g₁ ≫ f _ = g₂ ≫ f _ → x _ ≫ P.map g₁.op = x _ ≫ P.map g₂.op),
∃! t : T ⟶ P.obj (op B), ∀ i, t ≫ P.map (f i).op = x _

lemma subsingleton_of_empty_of_is_ExtrSheaf_of_types
  (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) (hF : is_ExtrSheaf_of_types F) (Z : ExtrDisc)
  [hZ : is_empty Z] : subsingleton (F.obj (op Z)) :=
begin
  constructor,
  intros a b,
  specialize hF Z pempty pempty.elim (λ a, a.elim) hZ.elim (λ a, a.elim) (λ a, a.elim),
  obtain ⟨t,h1,h2⟩ := hF,
  have : a = t, { apply h2, intros i, exact i.elim },
  have : b = t, { apply h2, intros i, exact i.elim },
  cc,
end

lemma finite_product_condition_for_types_of_is_ExtrSheaf_of_types
  (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) (hF : is_ExtrSheaf_of_types F) :
    ExtrDisc.finite_product_condition_for_types F :=
begin
  introsI ι _ X,
  have hF' := hF,
  specialize hF (ExtrDisc.sigma X) ι X (ExtrDisc.sigma.ι _)
    (ExtrDisc.sigma.ι_jointly_surjective _),
  split,
  { intros x y hh,
    dsimp at hh,
    have hx := hF (λ i, F.map (ExtrDisc.sigma.ι X i).op x) _,
    swap,
    { intros i j Z g₁ g₂ hh,
      dsimp,
      change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _,
      simp only [← F.map_comp, ← op_comp],
      rw hh },
    have hy := hF (λ i, F.map (ExtrDisc.sigma.ι X i).op y) _,
    swap,
    { intros i j Z g₁ g₂ hh,
      dsimp,
      change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _,
      simp only [← F.map_comp, ← op_comp],
      rw hh },
    obtain ⟨tx,htx1,htx2⟩ := hx,
    obtain ⟨ty,hty1,hty2⟩ := hy,
    have : x = tx,
    { apply htx2,
      intros i,
      refl },
    rw this,
    symmetry,
    apply htx2,
    intros i,
    apply_fun (λ e, e i) at hh,
    exact hh.symm },
  { intros x,
    have hx := hF x _,
    swap,
    { intros i j Z g₁ g₂ hh,
      by_cases hZ : nonempty Z,
      { obtain ⟨z⟩ := hZ,
        have : i = j,
        { apply_fun (λ e, (e z).1) at hh, exact hh },
        subst this,
        have : g₁ = g₂,
        { ext t : 2,
          apply_fun ExtrDisc.sigma.ι X i,
          swap,
          { apply Profinite.sigma.ι_injective },
          apply_fun (λ e, e t) at hh,
          exact hh },
        rw this },
      { simp at hZ, resetI,
        haveI := subsingleton_of_empty_of_is_ExtrSheaf_of_types F hF' Z,
        apply subsingleton.elim } },
    obtain ⟨t,ht,_⟩ := hx,
    use t,
    ext1,
    apply ht }
end

namespace product_condition_setup
section

parameters {P : ExtrDisc.{u}ᵒᵖ ⥤ Type w} (hP : ExtrDisc.finite_product_condition_for_types P)
parameters {B : ExtrDisc.{u}} {ι : Type u} [fintype ι] (X : ι → ExtrDisc.{u}) (f : Π i, X i ⟶ B)

def G : ι × ι → ExtrDisc := λ ii, (Profinite.pullback (f ii.1).val (f ii.2).val).pres
def gfst : Π ii : ι × ι, G ii ⟶ X ii.1 := λ ii, ⟨Profinite.pres_π _ ≫ Profinite.pullback.fst _ _⟩
def gsnd : Π ii : ι × ι, G ii ⟶ X ii.2 := λ ii, ⟨Profinite.pres_π _ ≫ Profinite.pullback.snd _ _⟩

lemma hX : function.bijective
  (λ (x : P.obj (op (ExtrDisc.sigma X))) (i : ι), P.map (ExtrDisc.sigma.ι X i).op x) := hP ι X
lemma hG : function.bijective
  (λ (x : P.obj (op (ExtrDisc.sigma G))) (i : ι × ι), P.map (ExtrDisc.sigma.ι G i).op x) := hP (ι × ι) G

def π : ExtrDisc.sigma X ⟶ B := ExtrDisc.sigma.desc X f

lemma hπ  (surj : ∀ b : B, ∃ i (x : X i), f i x = b) : function.surjective π :=
begin
  intros b,
  have := surj,
  obtain ⟨i,x,hx⟩ := surj b,
  use ExtrDisc.sigma.ι X i x,
  exact hx
end

def r : (ExtrDisc.sigma G).val ⟶ Profinite.pullback π.val π.val :=
begin
  refine Profinite.pullback.lift _ _ _ _ _,
  { refine Profinite.sigma.desc _ _,
    intros ii,
    refine _ ≫ Profinite.sigma.ι _ ii.1,
    refine (gfst _ _ _).val },
  { refine Profinite.sigma.desc _ _,
    intros ii,
    refine _ ≫ Profinite.sigma.ι _ ii.2,
    dsimp,
    refine (gsnd _ _ _).val },
  { apply Profinite.sigma.hom_ext,
    rintros ⟨i,j⟩,
    dsimp [π, ExtrDisc.sigma.desc, gfst, gsnd],
    simp [Profinite.pullback.condition] },
end

lemma hr : function.surjective r :=
begin
  rintros ⟨⟨⟨i,a⟩,⟨j,b⟩⟩,h⟩,
  dsimp [π, ExtrDisc.sigma.desc, Profinite.sigma.desc] at a b h,
  let ab : Profinite.pullback (f i).val (f j).val := ⟨⟨a,b⟩,h⟩,
  obtain ⟨c,hc⟩ := Profinite.pres_π_surjective _ ab,
  use ExtrDisc.sigma.ι (G X f) (i,j) c,
  apply subtype.ext,
  apply prod.ext,
  { apply sigma.ext, { refl },
    apply heq_of_eq,
    change (((Profinite.pullback (f i).val (f j).val).pres_π) c).val.fst = _,
    rw hc, refl },
  { apply sigma.ext, { refl },
    apply heq_of_eq,
    change (((Profinite.pullback (f i).val (f j).val).pres_π) c).val.snd = _,
    rw hc, refl }
end

@[nolint def_lemma] -- this lemma has an extremely annoying type to write down
def hE (surj : ∀ b : B, ∃ i (x : X i), f i x = b) :=
  ExtrDisc.equalizer_condition_for_types_holds P π (hπ surj) r hr

def QX : P.obj (op (ExtrDisc.sigma X)) ≃ Π i, P.obj (op (X i)) :=
  equiv.of_bijective _ hX
def QG : P.obj (op (ExtrDisc.sigma G)) ≃ Π ii, P.obj (op (G ii)) :=
  equiv.of_bijective _ hG

def rfst : ExtrDisc.sigma G ⟶ ExtrDisc.sigma X :=
  ⟨r ≫ Profinite.pullback.fst _ _⟩
def rsnd : ExtrDisc.sigma G ⟶ ExtrDisc.sigma X :=
  ⟨r ≫ Profinite.pullback.snd _ _⟩

lemma ι_rfst (ii : ι × ι) : ExtrDisc.sigma.ι G ii ≫ rfst =
  gfst ii ≫ ExtrDisc.sigma.ι _ _ :=
begin
  ext1,
  dsimp [rfst, gfst, ExtrDisc.sigma.ι, ExtrDisc.sigma.desc, r],
  simp [Profinite.pullback.condition, Profinite.pullback.condition_assoc],
end

lemma ι_rsnd (ii : ι × ι) : ExtrDisc.sigma.ι G ii ≫ rsnd =
  gsnd ii ≫ ExtrDisc.sigma.ι _ _ :=
begin
  ext1,
  dsimp [rsnd, gsnd, ExtrDisc.sigma.ι, ExtrDisc.sigma.desc, r],
  simp [Profinite.pullback.condition, Profinite.pullback.condition_assoc],
end

lemma QX_symm_ι_aux (q : Π i, P.obj (op (X i))) :
  q = λ i, P.map (ExtrDisc.sigma.ι X i).op (QX.symm q) :=
begin
  apply_fun (QX hP X).symm,
  change _ = (QX hP X).symm ((QX hP X) _),
  rw equiv.symm_apply_apply,
end

lemma QX_symm_ι (q : Π i, P.obj (op (X i))) (i : ι) :
  P.map (ExtrDisc.sigma.ι X i).op (QX.symm q) = q i :=
begin
  revert i,
  rw ← function.funext_iff,
  change _ = q,
  symmetry,
  apply QX_symm_ι_aux hP X q,
end

lemma QX_QG_compat_fst (q : Π i, P.obj (op (X i))) (i : ι × ι) :
  QG (P.map rfst.op (QX.symm q)) i = P.map (gfst i).op (q i.fst) :=
begin
  dsimp [QG],
  change (P.map _ ≫ P.map _) _ = _,
  simp only [← P.map_comp, ← op_comp, ι_rfst],
  simp only [P.map_comp, op_comp],
  dsimp,
  rw QX_symm_ι,
end

lemma QX_QG_compat_snd (q : Π i, P.obj (op (X i))) (i : ι × ι) :
  QG (P.map rsnd.op (QX.symm q)) i = P.map (gsnd i).op (q i.snd) :=
begin
  dsimp [QG],
  change (P.map _ ≫ P.map _) _ = _,
  simp only [← P.map_comp, ← op_comp, ι_rsnd],
  simp only [P.map_comp, op_comp],
  dsimp,
  rw QX_symm_ι,
end

end
end product_condition_setup

open product_condition_setup

theorem is_ExtrSheaf_of_types_of_finite_product_condition_for_types
  (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) (hF : ExtrDisc.finite_product_condition_for_types F) :
  is_ExtrSheaf_of_types F :=
begin
  introsI B ι _ X f surj x hx,
  have hrfst : ∀ (q : Π i, F.obj (op (X i))),
    (QG hF X f) (F.map (rfst X f).op ((QX hF X).symm q)) =
    (λ ii, F.map (gfst X f ii).op (q ii.1)),
  { intros q, funext ii,
    change (F.map _ ≫ F.map _) _ = _,
    simp only [← F.map_comp, ← op_comp, ι_rfst],
    simp only [F.map_comp, op_comp],
    dsimp,
    rw QX_symm_ι hF X q },
  have hrgsnd : ∀ (q : Π i, F.obj (op (X i))),
    (QG hF X f) (F.map (rsnd X f).op ((QX hF X).symm q)) =
    (λ ii, F.map (gsnd X f ii).op (q ii.2)),
  { intros q, funext ii,
    change (F.map _ ≫ F.map _) _ = _,
    simp only [← F.map_comp, ← op_comp, ι_rsnd],
    simp only [F.map_comp, op_comp],
    dsimp,
    rw QX_symm_ι hF X q },
  let EE : F.obj (op B) ≃
    { t : F.obj (op (ExtrDisc.sigma X)) // F.map (rfst X f).op t = F.map (rsnd X f).op t } :=
      equiv.of_bijective _ (hE X f surj),
  let x' : F.obj (op (ExtrDisc.sigma X)) := (QX hF X).symm x,
  -- Should follow from hx,
  have hx' : F.map (rfst X f).op x' = F.map (rsnd X f).op x',
  { apply_fun (QG hF X f),
    funext ii,
    rw QX_QG_compat_fst,
    rw QX_QG_compat_snd,
    apply hx,
    ext1,
    dsimp [gfst, gsnd],
    simp [Profinite.pullback.condition] },
  let b : F.obj (op B) := EE.symm ⟨x',hx'⟩,
  use b,
  have hb : ∀ i, F.map (f i).op b = x i,
  { intros i,
    have : f i = ExtrDisc.sigma.ι X i ≫ (π X f),
    { dsimp [π], rw ExtrDisc.sigma.ι_desc },
    rw [this, op_comp, F.map_comp],
    dsimp,
    have : F.map (π X f).op b = x',
    { change ↑(EE b) = x',
      dsimp only [b],
      rw equiv.apply_symm_apply,
      refl },
    rw this,
    dsimp [x'],
    change ((QX hF X) ((QX hF X).symm x)) _ = _,
    rw equiv.apply_symm_apply },
  refine ⟨hb, _⟩,
  { intros b' hb',
    apply_fun EE,
    ext1,
    apply_fun (QX hF X),
    dsimp [EE, QX, π],
    funext i,
    change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _,
    simp only [← F.map_comp, ← op_comp, ExtrDisc.sigma.ι_desc, hb, hb'] }
end

theorem is_ExtrSheaf_of_types_iff_product_condition_for_types (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) :
  is_ExtrSheaf_of_types F ↔ ExtrDisc.finite_product_condition_for_types F :=
begin
  split,
  { intro h, exact finite_product_condition_for_types_of_is_ExtrSheaf_of_types _ h },
  { intro h, exact is_ExtrSheaf_of_types_of_finite_product_condition_for_types _ h }
end

lemma is_ExtrSheaf_iff_forall_yoneda (F : ExtrDisc.{u}ᵒᵖ ⥤ C) :
  is_ExtrSheaf F ↔ (∀ (T : C), is_ExtrSheaf_of_types (F ⋙ coyoneda.obj (op T))) :=
begin
  split,
  { introsI h T B ι _ X f surj x hx,
    exact h B ι X f surj T x hx },
  { introsI h B ι _ X f surj T x hx,
    exact h T B ι X f surj x hx }
end

theorem finite_product_condition_iff_forall_yoneda [limits.has_finite_products C]
  (F : ExtrDisc.{u}ᵒᵖ ⥤ C) :
  ExtrDisc.finite_product_condition F ↔
  (∀ (T : C), ExtrDisc.finite_product_condition_for_types (F ⋙ coyoneda.obj (op T))) :=
begin
  split,
  { introsI h T ι _ X,
    let t : F.obj (op (ExtrDisc.sigma X)) ⟶ ∏ λ (i : ι), F.obj (op (X i)) :=
      limits.pi.lift (λ (i : ι), F.map (ExtrDisc.sigma.ι X i).op),
    specialize h ι X,
    dsimp at h ⊢,
    change is_iso t at h,
    resetI,
    split,
    { intros a b hab,
      dsimp at hab,
      suffices : a ≫ t = b ≫ t,
      { apply_fun (λ e, e ≫ inv t) at this, simpa using this },
      ext1,
      rw function.funext_iff at hab,
      simp [hab] },
    { intros a,
      use limits.pi.lift a ≫ inv t,
      dsimp,
      funext i,
      have : inv t ≫ F.map (ExtrDisc.sigma.ι X i).op = limits.pi.π _ i,
      { simp [is_iso.inv_comp_eq] },
      simp [this] } },
  { introsI h ι _ X,
    dsimp,
    let h₁ := h (∏ λ (i : ι), F.obj (op (X i))) ι X,
    let h₂ := h (F.obj (op (ExtrDisc.sigma X))) ι X,
    dsimp at h₁ h₂,
    replace h₁ := h₁.2,
    replace h₂ := h₂.1,
    obtain ⟨s,hs⟩ := h₁ (λ i, limits.pi.π _ i),
    use s,
    rw function.funext_iff at hs,
    dsimp at *,
    split,
    { apply h₂,
      ext1 i,
      dsimp,
      simp [hs i] },
    { ext1 i,
      simp [hs i] } }
end

theorem is_ExtrSheaf_iff_product_condition
  [limits.has_finite_products C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C) :
  is_ExtrSheaf F ↔ ExtrDisc.finite_product_condition F :=
begin
  rw is_ExtrSheaf_iff_forall_yoneda,
  rw finite_product_condition_iff_forall_yoneda,
  apply forall_congr (λ T, _),
  apply is_ExtrSheaf_of_types_iff_product_condition_for_types
end
