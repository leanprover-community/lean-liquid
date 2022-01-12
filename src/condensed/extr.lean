import topology.category.Profinite.projective
import for_mathlib.Profinite.product

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

universe u

structure ExtrDisc :=
(val : Profinite.{u})
[cond : projective val]

namespace ExtrDisc

@[simps]
instance : category ExtrDisc :=
{ hom := λ X Y, X.val ⟶ Y.val,
  id := λ X, 𝟙 _,
  comp := λ X Y Z f g, f ≫ g }

@[simps]
def _root_.ExtrDisc_to_Profinite : ExtrDisc ⥤ Profinite :=
{ obj := val,
  map := λ X Y f, f }

instance : concrete_category ExtrDisc.{u} :=
{ forget := ExtrDisc_to_Profinite ⋙ forget _,
  forget_faithful := ⟨⟩ }

instance : has_coe_to_sort ExtrDisc Type* :=
concrete_category.has_coe_to_sort _

instance {X Y : ExtrDisc} : has_coe_to_fun (X ⟶ Y) (λ f, X → Y) :=
⟨λ f, f⟩

instance (X : ExtrDisc) : projective X.val := X.cond

example (X : ExtrDisc) : projective (ExtrDisc_to_Profinite.obj X) :=
by { dsimp, apply_instance }

noncomputable
def split {X Y : ExtrDisc} (f : X ⟶ Y) (hf : function.surjective f) :
  Y ⟶ X :=
begin
  let f' : X.val ⟶ Y.val := f,
  have : epi f', by  rwa Profinite.epi_iff_surjective f',
  resetI,
  choose g h using projective.factors (𝟙 Y.val) f,
  exact ⟨g⟩,
end

@[simp, reassoc]
lemma splitting_is_splitting {X Y : ExtrDisc} (f : X ⟶ Y)
  (hf : function.surjective f) : split f hf ≫ f = 𝟙 _ :=
begin
  let f' : X.val ⟶ Y.val := f,
  have : epi f', by  rwa Profinite.epi_iff_surjective f',
  resetI,
  exact (projective.factors (𝟙 Y.val) f).some_spec,
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

noncomputable
def free.lift {X : ExtrDisc.{u}} {α : Type u} (f : α → X) : free α ⟶ X :=
⟨ultrafilter.extend f, continuous_ultrafilter_extend _⟩

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
  ext1,
  have := this.equalizer _ _ h,
  erw this,
  exact g.continuous,
  exact (free.lift f).continuous,
end

@[ext]
lemma free.hom_ext {X : ExtrDisc.{u}} {α : Type u} (f g : free α ⟶ X)
  (h : f ∘ (free.ι α) = g ∘ (free.ι α)) : f = g :=
by rw [free.lift_unique _ f rfl, free.lift_unique _ g rfl, h]

@[simps]
noncomputable
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

noncomputable
def adjunction : free_functor ⊣ forget _ :=
adjunction.mk_of_hom_equiv $
{ hom_equiv := λ α X,
  { to_fun := λ f, f ∘ free.ι _,
    inv_fun := λ f, free.lift f,
    left_inv := λ f, by { ext, dsimp, simp },
    right_inv := λ f, by { ext, dsimp, simp } },
  hom_equiv_naturality_left_symm' := λ _ _ _ _ _, by { ext, dsimp, simp },
  hom_equiv_naturality_right' := λ _ _ _ _ _, by { ext, dsimp, simp } }

end ExtrDisc
