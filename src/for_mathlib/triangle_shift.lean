import category_theory.triangulated.pretriangulated
import for_mathlib.homological_complex_shift
import for_mathlib.monoidal_category

noncomputable theory

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v u

-- Move + generalize!
@[simp]
lemma category_theory.discrete.associator_def (a b c : discrete ℤ) :
  α_ a b c = eq_to_iso (add_assoc a b c) := rfl

-- Move + generalize!
@[simp]
lemma category_theory.discrete.left_unitor_def (a : discrete ℤ) :
  λ_ a = eq_to_iso (zero_add _) := rfl

-- Move + generalize!
@[simp]
lemma category_theory.discrete.right_unitor_def (a : discrete ℤ) :
  ρ_ a = eq_to_iso (add_zero _) := rfl

namespace category_theory.triangulated
open category_theory.category

variables (C : Type u) [category.{v} C] [preadditive C]
variables [has_shift C ℤ]

local attribute [instance, reducible] endofunctor_monoidal_category

namespace triangle

@[simps]
def triangle_shift_obj (T : triangle C) (i : ℤ) : triangle C :=
triangle.mk C
  (i.neg_one_pow • ((shift_functor _ i).map T.mor₁))
  (i.neg_one_pow • (((shift_functor _ i).map T.mor₂)))
  (i.neg_one_pow • ((shift_functor C i).map T.mor₃ ≫ (shift_comm _ _ _).hom))

@[simps]
def triangle_shift_map {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) :
  triangle_shift_obj C T₁ i ⟶ triangle_shift_obj C T₂ i :=
{ hom₁ := (shift_functor _ i).map f.hom₁,
  hom₂ := (shift_functor _ i).map f.hom₂,
  hom₃ := (shift_functor _ i).map f.hom₃,
  comm₁' := by { dsimp, simp only [functor.map_zsmul,
    preadditive.zsmul_comp, preadditive.comp_zsmul, ← functor.map_comp, f.comm₁] },
  comm₂' := by { dsimp, simp only [functor.map_zsmul,
    preadditive.zsmul_comp, preadditive.comp_zsmul, ← functor.map_comp, f.comm₂] },
  comm₃' := begin
    dsimp,
    simp only [functor.map_zsmul,
      preadditive.zsmul_comp, preadditive.comp_zsmul],
    congr' 1,
    simp only [ shift_comm_hom_comp, assoc, iso.cancel_iso_hom_right_assoc,
      ← functor.map_comp, f.comm₃],
  end }

@[simps]
def triangle_shift_functor (i : ℤ) : triangle C ⥤ triangle C :=
{ obj := λ T, triangle_shift_obj C T i,
  map := λ T₁ T₂ f, triangle_shift_map C f _,
  map_id' := begin
    intros T,
    ext,
    all_goals { dsimp, simp },
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    ext,
    all_goals { dsimp, simp },
  end, } .

variable {C}

@[simps]
def iso.of_components {T₁ T₂ : triangle C}
  (e₁ : T₁.obj₁ ≅ T₂.obj₁)
  (e₂ : T₁.obj₂ ≅ T₂.obj₂)
  (e₃ : T₁.obj₃ ≅ T₂.obj₃) (h₁ h₂ h₃) : T₁ ≅ T₂ :=
{ hom :=
  { hom₁ := e₁.hom,
    hom₂ := e₂.hom,
    hom₃ := e₃.hom,
    comm₁' := h₁,
    comm₂' := h₂,
    comm₃' := h₃ },
  inv :=
  { hom₁ := e₁.inv,
    hom₂ := e₂.inv,
    hom₃ := e₃.inv,
    comm₁' := by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, h₁],
    comm₂' := by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, h₂],
    comm₃' := by rw [← functor.map_iso_inv, iso.comp_inv_eq, category.assoc, iso.eq_inv_comp,
      functor.map_iso_hom, h₃], },
  hom_inv_id' := by ext; dsimp; simp,
  inv_hom_id' := by ext; dsimp; simp }
.

variable (C)

@[simps]
def triangle_shift_functor_ε : 𝟭 (triangulated.triangle C) ≅ triangle_shift_functor C 0 :=
nat_iso.of_components (λ T,
  iso.of_components
    (shift_zero _ _).symm
    (shift_zero _ _).symm
    (shift_zero _ _).symm
    begin
      convert ((shift_functor_zero _ _).inv.naturality _),
      dsimp only [triangle_shift_functor, triangle_shift_obj],
      simpa,
    end
    begin
      convert ((shift_functor_zero _ _).inv.naturality _),
      dsimp only [triangle_shift_functor, triangle_shift_obj],
      simpa,
    end
    begin
      dsimp,
      rw one_smul,
      rw ← nat_trans.naturality_assoc, dsimp [shift_comm],
      simp only [obj_ε_app, discrete.functor_map_id, nat_trans.id_app, ε_app_obj, assoc, id_comp],
      rw [← nat_trans.comp_app, ← nat_trans.comp_app],
      erw [monoidal_functor.μ_inv_hom_id_assoc, id_comp], refl,
    end)
  begin
    intros T₁ T₂ f, ext;
    { dsimp only [triangle_morphism.comp_hom₁, iso.of_components_hom_hom₁, triangle_shift_map_hom₁,
        triangle_morphism.comp_hom₂, iso.of_components_hom_hom₂, triangle_shift_map_hom₂,
        triangle_morphism.comp_hom₃, iso.of_components_hom_hom₃, triangle_shift_map_hom₃,
        functor.id_map, triangle_category_comp, iso.symm_hom, iso.app_inv, iso.symm_inv,
        monoidal_functor.ε_iso_hom, triangle_shift_functor_map],
      rw ← nat_trans.naturality _ _, refl },
  end
.

variables [∀ (i : ℤ), (shift_functor C i).additive]

@[simps]
def shift_comm_functor (i j : ℤ) :
  shift_functor C i ⋙ shift_functor C j ≅ shift_functor C j ⋙ shift_functor C i :=
nat_iso.of_components
(λ X, shift_comm _ _ _)
sorry

lemma triangle_shift_functor_μ_aux (X : C) (i j : ℤ) :
  (shift_functor C j).map (shift_comm X 1 i).hom ≫
    (shift_comm ((shift_functor C i).obj X) 1 j).hom ≫
      (shift_functor C 1).map
        (shift_add X i j).inv =
  (shift_add ((shift_functor C 1).obj X) i j).inv ≫
    (shift_comm X 1 (i + j)).hom :=
begin
  simp only [iso.eq_inv_comp, ← category.assoc, ← functor.map_iso_inv,
    iso.comp_inv_eq],
  dsimp,
  simp only [category.assoc],
  dsimp [shift_comm],
  --simp only [← nat_trans.comp_app],
  change (shift_functor C j).map ((shift_comm_functor _ _ _).hom.app X) ≫
    (shift_comm_functor _ _ _).hom.app _ = _ ≫ (shift_comm_functor _ _ _).hom.app X ≫ _,
  have := (shift_comm_functor C 1 (i + j)).hom.naturality,
  dsimp only [functor.comp_map] at this,
  --- UUUUUGGGHHHHH
  sorry
end

@[simps]
def triangle_shift_functor_μ (i j : ℤ) :
  triangle_shift_functor C i ⋙ triangle_shift_functor C j ≅
    triangle_shift_functor C (i + j) :=
nat_iso.of_components (λ T,
  iso.of_components
    (shift_add _ _ _).symm
    (shift_add _ _ _).symm
    (shift_add _ _ _).symm
    (by sorry; begin
      dsimp [triangle_shift_functor, triangle_shift_obj],
      simp only [zsmul_comp, comp_zsmul, iso.symm_hom, iso.app_inv, iso.symm_inv,
        monoidal_functor.μ_iso_hom, functor.map_zsmul, smul_smul, int.neg_one_pow_add],
      have := ((shift_functor_add _ i j).inv.naturality T.mor₁),
      rw [functor.comp_map] at this,
      erw [this, mul_comm], refl,
    end)
    (by sorry; begin
      dsimp [triangle_shift_functor, triangle_shift_obj],
      simp only [zsmul_comp, comp_zsmul, iso.symm_hom, iso.app_inv, iso.symm_inv,
        monoidal_functor.μ_iso_hom, functor.map_zsmul, smul_smul, int.neg_one_pow_add],
      have := ((shift_functor_add _ i j).inv.naturality T.mor₂),
      rw [functor.comp_map] at this,
      erw [this, mul_comm], refl,
    end)
    begin
      dsimp [triangle_shift_functor, triangle_shift_obj],
      simp only [zsmul_comp, comp_zsmul, iso.symm_hom, iso.app_inv, iso.symm_inv,
        monoidal_functor.μ_iso_hom, functor.map_zsmul, smul_smul, int.neg_one_pow_add,
        mul_comm j.neg_one_pow],
      have := ((shift_functor_add _ i j).inv.naturality T.mor₃),
      dsimp [functor.comp_map] at this,
      erw [← reassoc_of this], clear this,
      simp only [functor.map_comp, assoc, obj_μ_app],
      congr' 2,
      --have := (shift_monoidal_functor C ℤ).to_lax_monoidal_functor.associativity i j 1,
      rw (shift_monoidal_functor C ℤ).map_associator_inv,
      dsimp,
      simp only [assoc, is_iso.inv_id, nat_trans.hcomp_app, comp_id, id_comp],
      slice_lhs 4 5
      { rw [← nat_trans.comp_app, is_iso.hom_inv_id,
          nat_trans.id_app] },
      erw id_comp,
      rw category_theory.nat_iso.is_iso_inv_app,
      --rw nat_trans.id_hcomp_app,
      dsimp,
      simp only [category_theory.functor.map_id, comp_id, assoc, is_iso.hom_inv_id_assoc],
      slice_lhs 4 5
      { rw [← nat_trans.comp_app, (shift_monoidal_functor C ℤ).μ_hom_inv_id,
          nat_trans.id_app] },
      erw comp_id, apply triangle_shift_functor_μ_aux,


      --     erw [category_theory.functor.map_id, comp_id],
      --dsimp [shift_comm],
      --simp only [← nat_trans.comp_app, is_iso.hom_inv_id_assoc],
      --erw is_iso.hom_inv_id_assoc,
      --erw comp_id,
      --rw category_theory.discrete.associator_def,
      --dsimp [shift_comm],
      --repeat { rw [← nat_trans.comp_app], },
      -- have := (shift_monoidal_functor C ℤ).to_lax_monoidal_functor.associativity i j 1,
    end)
  (by sorry; begin
    intros T₁ T₂ f, ext;
    { dsimp only [triangle_morphism.comp_hom₁, iso.of_components_hom_hom₁, triangle_shift_map_hom₁,
        triangle_morphism.comp_hom₂, iso.of_components_hom_hom₂, triangle_shift_map_hom₂,
        triangle_morphism.comp_hom₃, iso.of_components_hom_hom₃, triangle_shift_map_hom₃,
        functor.id_map, triangle_category_comp, iso.symm_hom, iso.app_inv, iso.symm_inv,
        monoidal_functor.ε_iso_hom, triangle_shift_functor_map],
      rw ← nat_trans.naturality _ _, refl },
  end)
.

/-
def triangle_shift_core : shift_mk_core (triangle C) ℤ :=
{ F := triangle_shift_functor _,
  ε := triangle_shift_functor_ε _,
  μ := λ i j, triangle_shift_functor_μ _ _ _,
  associativity := begin
    intros i j k T, ext,
    { have := (shift_monoidal_functor C ℤ).to_lax_monoidal_functor.associativity i j k,
      apply_fun (λ α, α.app T.obj₁) at this,
      simp only [nat_trans.comp_app, obj_μ_app, assoc, μ_inv_hom_app_assoc, map_inv_hom_app,
        comp_id, functor.associator_hom_app, nat_trans.hcomp_app, nat_trans.id_app,
        category_theory.functor.map_id, id_comp] at this,
      erw [id_comp] at this,
      refine eq.trans _ this, clear this,
      dsimp, simp only [obj_μ_app, assoc],
      -- I don't like that `(eq_to_hom _).hom₁`.
      sorry },
    sorry,
    sorry
  end,
  left_unitality := sorry,
  right_unitality := sorry }
-/

@[simps]
def map_triangle_shift_functor (m n : discrete ℤ) (f : m ⟶ n) :
  triangle_shift_functor C m ⟶ triangle_shift_functor C n :=
{ app := λ T,
  { hom₁ := eq_to_hom $ by rw discrete.eq_of_hom f,
    hom₂ := eq_to_hom $ by rw discrete.eq_of_hom f,
    hom₃ := eq_to_hom $ by rw discrete.eq_of_hom f,
    comm₁' := by { rcases f with ⟨⟨⟨⟩⟩⟩, simp only [eq_to_hom_refl, id_comp, comp_id], },
    comm₂' := by { rcases f with ⟨⟨⟨⟩⟩⟩, simp only [eq_to_hom_refl, id_comp, comp_id], },
    comm₃' := by { rcases f with ⟨⟨⟨⟩⟩⟩,
      dsimp, rw (shift_functor C (1 : ℤ)).map_id, simp only [comp_id, id_comp]} },
  naturality' := begin
    rcases f with ⟨⟨⟨⟩⟩⟩,
    rintros X Y g, ext;
    { dsimp, simp only [eq_to_hom_refl, id_comp, comp_id] },
  end } .



lemma associativity_aux (X : C) (a b c : discrete ℤ) :
(𝟙 ((shift_functor C c).obj ((shift_functor C b).obj ((shift_functor C a).obj X))) ≫
  (shift_functor C c).map (((shift_monoidal_functor C ℤ).to_lax_monoidal_functor.μ a b).app X)) ≫
  ((shift_monoidal_functor C ℤ).to_lax_monoidal_functor.μ (a ⊗ b) c).app X ≫
  eq_to_hom (by { congr' 2, apply add_assoc }) =
  𝟙 ((shift_functor C c).obj
  ((shift_functor C b).obj ((shift_functor C a).obj X))) ≫ (((shift_monoidal_functor C ℤ).to_lax_monoidal_functor.μ b c).app
  ((shift_functor C a).obj X) ≫ (shift_functor C (b + c)).map
  (𝟙 ((shift_functor C a).obj X))) ≫ ((shift_monoidal_functor C ℤ).to_lax_monoidal_functor.μ a
  (b ⊗ c)).app X :=
begin
  have := (shift_monoidal_functor C ℤ).associativity' a b c,
  apply_fun (λ e, e.app X) at this,
  dsimp at this ⊢,
  simp only [id_comp, comp_id, category_theory.functor.map_id,
    eq_to_hom_map, eq_to_hom_app] at this ⊢,
  erw comp_id,
  exact this
end

lemma left_unitality_aux (X : C) (a : discrete ℤ) : 𝟙 ((shift_functor C a).obj X) =
  (𝟙 ((shift_functor C a).obj X) ≫ (shift_functor C a).map
    ((shift_monoidal_functor C ℤ).to_lax_monoidal_functor.ε.app X)) ≫
    ((shift_monoidal_functor C ℤ).to_lax_monoidal_functor.μ
    (𝟙_ (discrete ℤ)) a).app X ≫ eq_to_hom (by { congr, exact zero_add a }) :=
begin
  have := (shift_monoidal_functor C ℤ).left_unitality' a,
  apply_fun (λ e, e.app X) at this,
  dsimp at this ⊢,
  simp only [id_comp, comp_id, category_theory.functor.map_id,
    eq_to_hom_map, eq_to_hom_app] at this ⊢,
  exact this
end

lemma right_unitality_aux (X : C) (a : discrete ℤ) : 𝟙 ((shift_functor C a).obj X) =
  ((shift_monoidal_functor C ℤ).to_lax_monoidal_functor.ε.app ((shift_functor C a).obj X) ≫
       (shift_functor C (𝟙_ (discrete ℤ))).map (𝟙 ((shift_functor C a).obj X))) ≫
    ((shift_monoidal_functor C ℤ).to_lax_monoidal_functor.μ a (𝟙_ (discrete ℤ))).app X ≫
    eq_to_hom (by { congr, apply add_zero }) :=
begin
  have := (shift_monoidal_functor C ℤ).right_unitality' a,
  apply_fun (λ e, e.app X) at this,
  dsimp at this ⊢,
  simp only [id_comp, comp_id, category_theory.functor.map_id,
    eq_to_hom_map, eq_to_hom_app] at this ⊢,
  erw comp_id,
  exact this
end

instance has_shift : has_shift (triangle C) ℤ := has_shift.mk $
{ obj := triangle_shift_functor _,
  map := λ m n f, map_triangle_shift_functor _ _ _ f,
  map_id' := λ X, by { ext; refl },
  map_comp' := λ X Y Z f g, by { ext; simp },
  ε := (triangle_shift_functor_ε _).hom,
  μ := λ m n, (triangle_shift_functor_μ _ m n).hom,
  μ_natural' := begin
    rintros m m' n n' ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩, ext;
    { dsimp, simp only [id_comp, comp_id, category_theory.functor.map_id] },
  end,
  associativity' := λ a b c, by ext; apply associativity_aux,
  left_unitality' := λ a, by ext; apply left_unitality_aux,
  right_unitality' := λ a, by ext; apply right_unitality_aux,
  ε_is_iso := infer_instance,
  μ_is_iso := infer_instance } .

@[simp]
lemma shift_obj₁ (T : triangle C) (i : ℤ) : T⟦i⟧.obj₁ = T.obj₁⟦i⟧ := rfl

@[simp]
lemma shift_obj₂ (T : triangle C) (i : ℤ) : T⟦i⟧.obj₂ = T.obj₂⟦i⟧ := rfl

@[simp]
lemma shift_obj₃ (T : triangle C) (i : ℤ) : T⟦i⟧.obj₃ = T.obj₃⟦i⟧ := rfl

@[simp]
lemma shift_mor₁ (T : triangle C) (i : ℤ) : T⟦i⟧.mor₁ = i.neg_one_pow • T.mor₁⟦i⟧' := rfl

@[simp]
lemma shift_mor₂ (T : triangle C) (i : ℤ) : T⟦i⟧.mor₂ = i.neg_one_pow • T.mor₂⟦i⟧' := rfl

@[simp]
lemma shift_mor₃ (T : triangle C) (i : ℤ) :
  T⟦i⟧.mor₃ = i.neg_one_pow • (T.mor₃⟦i⟧' ≫ (shift_comm _ _ _).hom) := rfl

@[simp]
lemma shift_hom₁ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₁ = f.hom₁⟦i⟧' := rfl

@[simp]
lemma shift_hom₂ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₂ = f.hom₂⟦i⟧' := rfl

@[simp]
lemma shift_hom₃ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₃ = f.hom₃⟦i⟧' := rfl

end triangle

/-
instance {C : Type*} [category C] [preadditive C] (X Y : C) : has_neg (X ≅ Y) :=
⟨λ f,
{ hom := -f.hom,
  inv := -f.inv,
  hom_inv_id' := by simp only [comp_neg, neg_comp, iso.hom_inv_id, neg_neg],
  inv_hom_id' := by simp only [comp_neg, neg_comp, iso.inv_hom_id, neg_neg] }⟩

@[simp] lemma _root_.category_theory.neg_hom
   {C : Type*} [category C] [preadditive C] {X Y : C} (f : X ≅ Y) :
   (-f).hom = -(f.hom) := rfl

@[simp] lemma _root_.category_theory.neg_inv
   {C : Type*} [category C] [preadditive C] {X Y : C} (f : X ≅ Y) :
   (-f).inv = -(f.inv) := rfl
-/

namespace pretriangulated

@[simp] lemma shift_comm_self (X : C) (i : ℤ) : shift_comm X i i = iso.refl _ :=
begin
  ext,
  dsimp [shift_comm, opaque_eq_to_iso],
  simp only [discrete.functor_map_id, nat_trans.id_app, id_comp, μ_hom_inv_app],
  refl,
end

@[elab_as_eliminator] protected lemma _root_.int.induction_on_iff {p : ℤ → Prop}
  (i : ℤ) (hz : p 0) (h : ∀ i : ℤ, p i ↔ p (i + 1)) : p i :=
begin
  induction i using int.induction_on with i IH i IH,
  { exact hz },
  { rwa ← h },
  { rw h, simpa only [sub_add_cancel], }
end

variables [has_zero_object C] [∀ (i : ℤ), (shift_functor C i).additive] [pretriangulated C]

lemma dist_triangle_iff_of_iso {T₁ T₂ : triangle C} (e : T₁ ≅ T₂) :
  (T₁ ∈ dist_triang C) ↔ (T₂ ∈ dist_triang C) :=
⟨λ h, isomorphic_distinguished _ h _ e.symm, λ h, isomorphic_distinguished _ h _ e⟩

lemma dist_triangle_rot_iff (T : triangle C) :
  (T.rotate ∈ dist_triang C) ↔ (T ∈ dist_triang C) :=
begin
  refine ⟨λ h, _, λ h, rot_of_dist_triangle _ _ h⟩,
  let e : T ≅ T.rotate.inv_rotate := rot_comp_inv_rot.app T,
  rw ← dist_triangle_iff_of_iso _ e.symm,
  exact inv_rot_of_dist_triangle _ _ h,
end

lemma shift_of_dist_triangle (T : triangle C) (hT : T ∈ dist_triang C) (i : ℤ) :
  T⟦i⟧ ∈ dist_triang C :=
begin
  induction i using int.induction_on_iff with i,
  { exact isomorphic_distinguished T hT _ (shift_zero _ _), },
  { suffices : T⟦(i+1 : ℤ)⟧ ≅ T⟦(i:ℤ)⟧.rotate.rotate.rotate,
    { dsimp,
      rw dist_triangle_iff_of_iso _ this,
      iterate 3 { rw dist_triangle_rot_iff }, },
    refine shift_add _ _ _ ≪≫ _,
    refine triangle.iso.of_components (iso.refl _) (iso.refl _) (iso.refl _) _ _ _,
    { dsimp, simp only [category.id_comp, category.comp_id, comp_neg, neg_one_smul], },
    { dsimp, simp only [category.id_comp, category.comp_id, neg_comp, neg_one_smul], },
    { dsimp, simp only [category.id_comp, category.comp_id, neg_comp, neg_one_smul],
      simp only [functor.map_comp, assoc, category_theory.functor.map_id, comp_id,
        functor.map_zsmul, preadditive.zsmul_comp, preadditive.comp_zsmul,
        shift_comm_self, iso.refl_hom], }, },
end

end pretriangulated

end category_theory.triangulated
