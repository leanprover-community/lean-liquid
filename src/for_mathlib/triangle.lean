import category_theory.triangulated.rotate

namespace category_theory

namespace triangulated

open category_theory.triangulated.triangle_morphism

variables {C : Type*} [category C] [has_shift C ℤ] {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂)

lemma triangle_morphism_is_iso [is_iso f.hom₁] [is_iso f.hom₂] [is_iso f.hom₃] :
  is_iso f :=
by { refine ⟨⟨⟨inv f.hom₁, inv f.hom₂, inv f.hom₃, _, _, _⟩, _, _⟩⟩; tidy }
.
instance [is_iso f] : is_iso f.hom₁ :=
by { refine ⟨⟨(inv f).hom₁, _, _⟩⟩; simpa only [← comp_hom₁, ← triangle_category_comp,
  is_iso.hom_inv_id, is_iso.inv_hom_id] }

instance [is_iso f] : is_iso f.hom₂ :=
by { refine ⟨⟨(inv f).hom₂, _, _⟩⟩; simpa only [← comp_hom₂, ← triangle_category_comp,
  is_iso.hom_inv_id, is_iso.inv_hom_id] }

instance [is_iso f] : is_iso f.hom₃ :=
by { refine ⟨⟨(inv f).hom₃, _, _⟩⟩; simpa only [← comp_hom₃, ← triangle_category_comp,
  is_iso.hom_inv_id, is_iso.inv_hom_id] }

@[simp] lemma inv_hom₁ [is_iso f] : (inv f).hom₁ = inv (f.hom₁) :=
by { ext, change (f ≫ inv f).hom₁ = _, rw is_iso.hom_inv_id, refl }

@[simp] lemma inv_hom₂ [is_iso f] : (inv f).hom₂ = inv (f.hom₂) :=
by { ext, change (f ≫ inv f).hom₂ = _, rw is_iso.hom_inv_id, refl }

@[simp] lemma inv_hom₃ [is_iso f] : (inv f).hom₃ = inv (f.hom₃) :=
by { ext, change (f ≫ inv f).hom₃ = _, rw is_iso.hom_inv_id, refl }

lemma triangle_morphism_is_iso_iff : is_iso f ↔
    is_iso f.hom₁ ∧ is_iso f.hom₂ ∧ is_iso f.hom₃ :=
begin
  split,
  { intro _, refine ⟨_, _, _⟩; exactI infer_instance },
  { rintro ⟨_, _, _⟩, exactI triangle_morphism_is_iso f }
end

@[simps]
def mk_triangle_iso (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₂ : T₁.obj₂ ≅ T₂.obj₂) (e₃ : T₁.obj₃ ≅ T₂.obj₃)
  (comm₁ : T₁.mor₁ ≫ e₂.hom = e₁.hom ≫ T₂.mor₁)
  (comm₂ : T₁.mor₂ ≫ e₃.hom = e₂.hom ≫ T₂.mor₂)
  (comm₃ : T₁.mor₃ ≫ e₁.hom⟦1⟧' = e₃.hom ≫ T₂.mor₃) : T₁ ≅ T₂ :=
⟨⟨_, _, _, comm₁, comm₂, comm₃⟩, ⟨e₁.inv, e₂.inv, e₃.inv,
  by { rw e₂.comp_inv_eq, simp [comm₁] }, by { rw e₃.comp_inv_eq, simp [comm₂] },
  by { rw [e₃.eq_inv_comp, ← category.assoc, ← comm₃], simp [← functor.map_comp] }⟩,
  by { ext; simp }, by { ext; simp }⟩

@[simps] noncomputable
def triangle.nonneg_inv_rotate (T : triangle C) : triangle C :=
triangle.mk _ (T.mor₃⟦(-1:ℤ)⟧' ≫ (shift_shift_neg _ _).hom) T.mor₁
  (T.mor₂ ≫ (shift_neg_shift _ _).inv)

@[simps]
def triangle.nonneg_rotate {C : Type*} [category C]
  [has_shift C ℤ] (T : triangle C) : triangle C := triangle.mk _ T.mor₂ T.mor₃ (T.mor₁⟦1⟧')

variables (C) [preadditive C]

@[simps]
def neg₃_functor : triangle C ⥤ triangle C :=
{ obj := λ T, triangle.mk C T.mor₁ T.mor₂ (-T.mor₃),
  map := λ S T f, { hom₁ := f.hom₁, hom₂ := f.hom₂, hom₃ := f.hom₃ } }

@[simps]
def neg₃_unit_iso : neg₃_functor C ⋙ neg₃_functor C ≅ 𝟭 _ :=
begin
  refine nat_iso.of_components
    (λ X, ⟨⟨𝟙 _, 𝟙 _, 𝟙 _, _, _, _⟩, ⟨𝟙 _, 𝟙 _, 𝟙 _, _, _, _⟩, _, _⟩) (λ X Y f, _),
  any_goals { ext },
  all_goals { dsimp,
    simp only [category.comp_id, category.id_comp, category_theory.functor.map_id, neg_neg] },
end

@[simps]
def neg₃_equiv : triangle C ≌ triangle C :=
{ functor := neg₃_functor C,
  inverse := neg₃_functor C,
  unit_iso := (neg₃_unit_iso C).symm,
  counit_iso := neg₃_unit_iso C }

--move this (do we want this?)
instance {C : Type*} [category C] [preadditive C] {X Y : C} : has_neg (X ≅ Y) :=
⟨λ e, ⟨-e.hom, -e.inv, by simp, by simp⟩⟩
.
@[simp] lemma neg_iso_hom {C : Type*} [category C] [preadditive C] {X Y : C} {e : X ≅ Y} :
  (-e).hom = -(e.hom) := rfl

@[simp] lemma neg_iso_inv {C : Type*} [category C] [preadditive C] {X Y : C} {e : X ≅ Y} :
  (-e).inv = -(e.inv) := rfl

--move this
@[simps]
def _root_.category_theory.equivalence.iso_equiv {C D : Type*} [category C] [category D]
  (e : C ≌ D) (X : C) (Y : D) : (e.functor.obj X ≅ Y) ≃ (X ≅ e.inverse.obj Y) :=
{ to_fun := λ f, e.unit_iso.app X ≪≫ e.inverse.map_iso f,
  inv_fun := λ f, e.functor.map_iso f ≪≫ e.counit_iso.app Y,
  left_inv := λ f, by { ext, dsimp, simp only [iso.inv_hom_id_app, category.assoc, functor.map_comp,
    e.fun_inv_map], rw reassoc_of e.functor_unit_iso_comp, dsimp, simp },
  right_inv := λ f, by { ext, dsimp, simp } }

variables {C} (T : triangle C)

noncomputable
def triangle.nonneg_inv_rotate_neg₃ [(shift_functor C (1 : ℤ)).additive] :
  (neg₃_functor C).obj T.nonneg_inv_rotate ≅ T.inv_rotate :=
begin
  fapply mk_triangle_iso,
  exact -iso.refl _,
  exact iso.refl _,
  exact iso.refl _,
  all_goals { dsimp, simp },
end

noncomputable
def triangle.nonneg_inv_rotate_iso [(shift_functor C (1 : ℤ)).additive] :
  T.nonneg_inv_rotate ≅ (neg₃_functor C).obj T.inv_rotate :=
(neg₃_equiv C).iso_equiv _ _ T.nonneg_inv_rotate_neg₃

@[simps]
def neg₃_rotate : neg₃_functor C ⋙ rotate ≅ rotate ⋙ neg₃_functor C :=
nat_iso.of_components
  (λ X, mk_triangle_iso (iso.refl _) (iso.refl _) (-iso.refl _)
    (by { dsimp, simp }) (by { dsimp, simp }) (by { dsimp, simp }))
  (λ X Y f, by { dsimp, ext; dsimp; simp })

lemma triangle.nonneg_rotate_neg₃ :
  (neg₃_functor C).obj T.nonneg_rotate = T.rotate := rfl

def triangle.nonneg_rotate_iso : T.nonneg_rotate ≅ (neg₃_functor C).obj T.rotate :=
(neg₃_equiv C).iso_equiv _ _ (iso.refl _)

--

@[simps]
def triangle.obj₁_functor : triangle C ⥤ C :=
{ obj := λ T, T.obj₁,
  map := λ S T f, f.hom₁,
  map_id' := λ _, rfl,
  map_comp' := λ A B C f g, rfl }

@[simps]
def triangle.obj₂_functor : triangle C ⥤ C :=
{ obj := λ T, T.obj₂,
  map := λ S T f, f.hom₂,
  map_id' := λ _, rfl,
  map_comp' := λ A B C f g, rfl }

@[simps]
def triangle.obj₃_functor : triangle C ⥤ C :=
{ obj := λ T, T.obj₃,
  map := λ S T f, f.hom₃,
  map_id' := λ _, rfl,
  map_comp' := λ A B C f g, rfl }

end triangulated

end category_theory
