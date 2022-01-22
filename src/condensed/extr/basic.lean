import topology.category.Profinite.projective
import for_mathlib.Profinite.disjoint_union

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
