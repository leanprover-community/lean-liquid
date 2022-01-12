import topology.category.Profinite.projective
import for_mathlib.Profinite.product

open category_theory

universe u

structure ExtrDisc :=
(val : Profinite.{u})
[cond : projective val]

namespace ExtrDisc

@[ext]
structure hom (X Y : ExtrDisc) :=
mk :: (val : X.val ⟶ Y.val)

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

instance (X : ExtrDisc) : projective X.val := X.cond

example (X : ExtrDisc) : projective (ExtrDisc_to_Profinite.obj X) :=
by { dsimp, apply_instance }

noncomputable
def split {X Y : ExtrDisc} (f : X ⟶ Y) (hf : function.surjective f.val) :
  Y ⟶ X :=
begin
  have : epi f.val, by rwa Profinite.epi_iff_surjective f.val,
  resetI,
  choose g h using projective.factors (𝟙 Y.val) f.val,
  exact ⟨g⟩,
end

@[simp, reassoc]
lemma splitting_is_splitting {X Y : ExtrDisc} (f : X ⟶ Y)
  (hf : function.surjective f.val) : split f hf ≫ f = 𝟙 _ :=
begin
  have : epi f.val, by rwa Profinite.epi_iff_surjective f.val,
  resetI,
  ext1,
  exact (projective.factors (𝟙 Y.val) f.val).some_spec,
end

instance : has_coe_to_sort ExtrDisc Type* :=
concrete_category.has_coe_to_sort _

instance {X Y : ExtrDisc} : has_coe_to_fun (X ⟶ Y) (λ f, X → Y) :=
concrete_category.has_coe_to_fun

@[simp]
lemma coe_fun_eq {X Y : ExtrDisc} (f : X ⟶ Y) : ⇑(f.val) = f := rfl

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

noncomputable
def free.lift {X : ExtrDisc.{u}} {α : Type u} (f : α → X) : free α ⟶ X :=
⟨⟨ultrafilter.extend f, continuous_ultrafilter_extend _⟩⟩

@[simp]
lemma free.ι_lift {X : ExtrDisc.{u}} {α : Type u} (f : α → X) :
  free.lift f ∘ free.ι _ = f :=
begin
  ext,
  dsimp [free.lift, free.ι],
  change (ultrafilter.extend _ ∘ pure) _ = _,
  rw ultrafilter_extend_extends,
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

end ExtrDisc
