import condensed.adjunctions
import condensed.extr.equivalence
import linear_algebra.tensor_product

import for_mathlib.endomorphisms.functor
import for_mathlib.AddCommGroup_instances
import for_mathlib.AddCommGroup.explicit_products

noncomputable theory

universes u
open_locale tensor_product

open category_theory

namespace AddCommGroup

def linear_equiv_to_iso {A B : AddCommGroup.{u}}
  (e : A ≃ₗ[ℤ] B) :
  A ≅ B :=
{ hom := e.to_linear_map.to_add_monoid_hom,
  inv := e.symm.to_linear_map.to_add_monoid_hom,
  hom_inv_id' := begin
    ext t,
    simp,
  end,
  inv_hom_id' := begin
    ext t,
    simp,
  end }

def tensor (A B : AddCommGroup.{u}) : AddCommGroup.{u} :=
AddCommGroup.of (A ⊗[ℤ] B)

def tensor_uncurry {A B C : AddCommGroup.{u}}
  (e : A ⟶ AddCommGroup.of (B ⟶ C)) : tensor A B ⟶ C :=
linear_map.to_add_monoid_hom $ tensor_product.lift $
let e' := e.to_int_linear_map,
  e'' : (B ⟶ C) →ₗ[ℤ] (B →ₗ[ℤ] C) :=
  add_monoid_hom.to_int_linear_map
  { to_fun := λ f, f.to_int_linear_map,
    map_zero' := by { ext, refl },
    map_add' := λ f g, by { ext, refl } } in
e''.comp e'

def tensor_curry {A B C : AddCommGroup.{u}}
  (e : tensor A B ⟶ C) : A ⟶ AddCommGroup.of (B ⟶ C) :=
{ to_fun := λ a,
  { to_fun := λ b, e (a ⊗ₜ b),
    map_zero' := by { rw [tensor_product.tmul_zero, e.map_zero], },
    map_add' := begin
      intros b c,
      rw [tensor_product.tmul_add, e.map_add],
    end },
  map_zero' := begin
    ext t,
    dsimp,
    rw [tensor_product.zero_tmul, e.map_zero],
  end,
  map_add' := begin
    intros x y, ext t,
    dsimp,
    rw [tensor_product.add_tmul, e.map_add],
  end }

.

@[simps]
def tensor_curry_equiv (A B C : AddCommGroup.{u}) :
  (tensor A B ⟶ C) ≃+ (A ⟶ (AddCommGroup.of (B ⟶ C))) :=
{ to_fun := tensor_curry,
  inv_fun := tensor_uncurry,
  left_inv := begin
    intros f,
    ext t,
    apply tensor_product.induction_on t,
    { simp, },
    { intros x y, dsimp [tensor_uncurry, tensor_curry],
      simp, },
    { intros x y h1 h2,
      simp only [map_add, h1, h2] }
  end,
  right_inv := λ f, by { ext, dsimp [tensor_uncurry, tensor_curry], simp, },
  map_add' := λ x y, by { ext, refl } }

def map_tensor {A A' B B' : AddCommGroup.{u}}
  (f : A ⟶ A') (g : B ⟶ B') : tensor A B ⟶ tensor A' B' :=
(tensor_product.map f.to_int_linear_map g.to_int_linear_map).to_add_monoid_hom

lemma id_helper (A : AddCommGroup.{u}) :
  (𝟙 A : A ⟶ A).to_int_linear_map = linear_map.id := rfl

lemma comp_helper {A B C : AddCommGroup.{u}}
  (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).to_int_linear_map = g.to_int_linear_map.comp f.to_int_linear_map := rfl

@[simp]
lemma zero_helper {A B : AddCommGroup.{u}} :
  (0 : A ⟶ B).to_int_linear_map = 0 := rfl

@[simp]
lemma map_tensor_id {A B : AddCommGroup.{u}} :
  map_tensor (𝟙 A) (𝟙 B) = 𝟙 _ :=
begin
  ext t, dsimp [map_tensor], simp [id_helper],
end

@[simp]
lemma map_tensor_comp_left {A A' A'' B : AddCommGroup.{u}} (f : A ⟶ A') (g : A' ⟶ A'') :
  map_tensor (f ≫ g) (𝟙 B) = map_tensor f (𝟙 _) ≫ map_tensor g (𝟙 _) :=
begin
  ext t,
  rw ← category.id_comp (𝟙 B),
  dsimp [map_tensor], simp only [comp_helper, id_helper, tensor_product.map_comp],
  simp,
end

@[simp]
lemma map_tensor_comp_right {A B B' B'' : AddCommGroup.{u}} (f : B ⟶ B') (g : B' ⟶ B'') :
  map_tensor (𝟙 A) (f ≫ g) = map_tensor (𝟙 _) f ≫ map_tensor (𝟙 _) g :=
begin
  ext t,
  rw ← category.id_comp (𝟙 A),
  dsimp [map_tensor], simp only [comp_helper, id_helper, tensor_product.map_comp],
  simp,
end

@[simp]
lemma map_tensor_comp_comp {A A' A'' B B' B'' : AddCommGroup.{u}}
  (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B'') :
  map_tensor (f ≫ f') (g ≫ g') = map_tensor f g ≫ map_tensor f' g' :=
begin
  ext t,
  dsimp [map_tensor], simp only [comp_helper, id_helper, tensor_product.map_comp],
  simp,
end

lemma map_tensor_eq_comp {A A' B B' : AddCommGroup.{u}} (f : A ⟶ A') (g : B ⟶ B') :
  map_tensor f g = map_tensor f (𝟙 _) ≫ map_tensor (𝟙 _) g :=
begin
  nth_rewrite 0 ← category.id_comp g,
  nth_rewrite 0 ← category.comp_id f,
  rw map_tensor_comp_comp,
end

lemma map_tensor_eq_comp' {A A' B B' : AddCommGroup.{u}} (f : A ⟶ A') (g : B ⟶ B') :
  map_tensor f g = map_tensor (𝟙 _) g ≫ map_tensor f (𝟙 _) :=
begin
  nth_rewrite 0 ← category.id_comp f,
  nth_rewrite 0 ← category.comp_id g,
  rw map_tensor_comp_comp,
end

@[simp]
lemma map_tensor_zero_left {A A' B B' : AddCommGroup.{u}} (f : B ⟶ B') :
  map_tensor (0 : A ⟶ A') f = 0 :=
begin
  apply (tensor_curry_equiv _ _ _).injective,
  ext a b,
  dsimp [tensor_curry, map_tensor],
  simp,
end

@[simp]
lemma map_tensor_zero_right {A A' B B' : AddCommGroup.{u}} (f : A ⟶ A') :
  map_tensor f (0 : B ⟶ B') = 0 :=
begin
  apply (tensor_curry_equiv _ _ _).injective,
  ext a b,
  dsimp [tensor_curry, map_tensor],
  simp,
end

lemma tensor_uncurry_curry {A B C D : AddCommGroup.{u}} (f : A ⟶ B) (g : B.tensor C ⟶ D) :
  tensor_uncurry (f ≫ tensor_curry g) = map_tensor f (𝟙 _) ≫ g :=
begin
  apply (tensor_curry_equiv _ _ _).injective,
  erw (tensor_curry_equiv _ _ _).apply_symm_apply,
  ext a c,
  dsimp [tensor_curry, tensor_curry_equiv, map_tensor],
  simp,
end

lemma tensor_curry_uncurry {A B C D : AddCommGroup.{u}}
  (e : A ⟶ AddCommGroup.of (B ⟶ C)) (g : C ⟶ D):
  tensor_curry (tensor_uncurry e ≫ g) =
  e ≫ (preadditive_yoneda.flip.obj (opposite.op B)).map g := sorry

@[simps]
def tensor_functor : AddCommGroup.{u} ⥤ AddCommGroup.{u} ⥤ AddCommGroup.{u} :=
{ obj := λ A,
  { obj := λ B, tensor A B,
    map := λ B B' f, map_tensor (𝟙 _) f,
    map_id' := λ A, map_tensor_id,
    map_comp' := λ A B C f g, map_tensor_comp_right _ _ },
  map := λ A A' f,
  { app := λ B, map_tensor f (𝟙 _),
    naturality' := λ B C g, begin
      dsimp,
      rw [← map_tensor_eq_comp, ← map_tensor_eq_comp'],
    end },
  map_id' := begin
    intros A,
    ext B : 2,
    dsimp, exact map_tensor_id,
  end,
  map_comp' := begin
    intros A B C f g,
    ext B : 2,
    dsimp, exact map_tensor_comp_left _ _,
  end }

def tensor_explicit_pi_comparison {α : Type u} [fintype α] (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  tensor (AddCommGroup.of (direct_sum α (λ i, X i))) B ⟶
  AddCommGroup.of (direct_sum α (λ i, tensor (X i) B)) :=
direct_sum_lift.{u u+1} _ $ λ a, map_tensor (direct_sum_π.{u u+1} _ _) (𝟙 _)

def tensor_pi_comparison {α : Type u} (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  tensor (∏ X) B ⟶ ∏ (λ a, tensor (X a) B) :=
limits.pi.lift $ λ b, map_tensor (limits.pi.π _ _) (𝟙 _)

open_locale classical

def tensor_explicit_pi_iso {α : Type u}
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  (of (direct_sum α (λ (i : α), ↥(X i)))).tensor B ≅
  of (direct_sum α (λ (i : α), ↥((X i).tensor B))) :=
{ hom := tensor_uncurry $ direct_sum_desc.{u u+1} X $ λ i, tensor_curry $
    direct_sum_ι.{u u+1} _ i,
  inv := direct_sum_desc.{u u+1} _ $ λ i,
    map_tensor (direct_sum_ι.{u u+1} X i) (𝟙 _),
  hom_inv_id' := begin
    apply (tensor_curry_equiv _ _ _).injective,
    ext a b,
    dsimp [tensor_curry, tensor_uncurry, direct_sum_desc],
    simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
      linear_map.coe_comp, add_monoid_hom.coe_to_int_linear_map, add_monoid_hom.coe_mk,
      direct_sum.to_add_monoid_of, id_apply],
    dsimp [direct_sum_ι],
    simp only [direct_sum.to_add_monoid_of],
    dsimp [map_tensor],
    simp only [id_apply],
  end,
  inv_hom_id' := begin
    apply direct_sum_hom_ext'.{u u+1},
    intros i,
    simp only [direct_sum_ι_desc_assoc, category.comp_id],
    apply (tensor_curry_equiv _ _ _).injective,
    ext a b k,
    dsimp [tensor_curry, direct_sum_ι, direct_sum.of, map_tensor,
      tensor_uncurry, tensor_curry, direct_sum_desc],
    simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.map_tmul,
      add_monoid_hom.coe_to_int_linear_map, dfinsupp.single_add_hom_apply, id_apply,
      tensor_product.lift.tmul, linear_map.coe_comp, add_monoid_hom.coe_mk,
      dfinsupp.single_apply],
    dsimp [direct_sum.to_add_monoid],
    simp only [dfinsupp.sum_add_hom_single, add_monoid_hom.coe_mk, dfinsupp.single_apply]
  end }

lemma tensor_explicit_pi_iso_hom_eq {α : Type u} [fintype α]
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  (tensor_explicit_pi_iso X B).hom = tensor_explicit_pi_comparison X B :=
begin
  symmetry,
  apply direct_sum_hom_ext.{u u+1}, swap, apply_instance,
  intros j,
  apply (tensor_curry_equiv _ _ _).injective,
  apply direct_sum_hom_ext'.{u u+1}, intros i,
  apply (tensor_curry_equiv _ _ _).symm.injective,
  dsimp,
  simp_rw tensor_uncurry_curry,
  erw [direct_sum_lift_π, ← map_tensor_comp_comp, category.id_comp],
  dsimp only [tensor_explicit_pi_iso],
  erw [← category.assoc], let t := _, change _ = t ≫ _,
  have ht : t = direct_sum_ι.{u u+1} _ i,
  { dsimp [t],
    have := direct_sum_ι_desc.{u u+1} (λ i, tensor (X i) B)
      (λ i, map_tensor (direct_sum_ι.{u u+1} _ i) (𝟙 _)) i,
    dsimp at this, rw ← this, clear this,
    rw category.assoc,
    erw [(tensor_explicit_pi_iso X B).inv_hom_id, category.comp_id] },
  rw ht, clear ht, clear t,
  by_cases i = j,
  { subst h,
    simp [direct_sum_ι_π.{u u+1}] },
  { simp [direct_sum_ι_π_of_ne.{u u+1} _ _ _ h], }
end

instance is_iso_tensor_explicit_pi_comparison {α : Type u} [fintype α]
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) : is_iso (tensor_explicit_pi_comparison X B) :=
begin
  rw ← tensor_explicit_pi_iso_hom_eq,
  apply_instance
end

lemma tensor_explicit_pi_comparison_comparison {α : Type u}
  [fintype α]
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  tensor_pi_comparison X B =
  map_tensor (direct_sum_lift.{u u+1} _ $ limits.pi.π _) (𝟙 _) ≫
  tensor_explicit_pi_comparison X B ≫
  limits.pi.lift (direct_sum_π.{u u+1} (λ i, tensor (X i) B)) :=
begin
  ext1,
  dsimp [tensor_pi_comparison],
  simp only [limits.limit.lift_π, limits.fan.mk_π_app, category.assoc],
  dsimp [tensor_explicit_pi_comparison],
  rw [direct_sum_lift_π, ← map_tensor_comp_left, direct_sum_lift_π],
end

instance is_iso_tensor_pi_comparison {α : Type u} [fintype α]
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) : is_iso (tensor_pi_comparison X B) :=
begin
  rw tensor_explicit_pi_comparison_comparison,
  apply_with is_iso.comp_is_iso { instances := ff },
  { change is_iso ((tensor_functor.flip.obj B).map _),
    apply_with functor.map_is_iso { instances := ff },
    change is_iso ((limits.limit.is_limit _).cone_point_unique_up_to_iso
      (is_limit_direct_sum_fan.{u u+1} X)).hom,
    apply_instance },
  apply_with is_iso.comp_is_iso { instances := ff }, apply_instance,
  change is_iso ((is_limit_direct_sum_fan.{u u+1} _).cone_point_unique_up_to_iso
    (limits.limit.is_limit _)).hom,
  apply_instance,
  apply_instance
end

def tensor_flip (A B : AddCommGroup.{u}) : A.tensor B ≅ B.tensor A :=
linear_equiv_to_iso (tensor_product.comm _ _ _)

end AddCommGroup

namespace ExtrSheafProd

/-- S ↦ M(S) ⊗ A -/
def tensor_presheaf (M : ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1} :=
M ⋙ AddCommGroup.tensor_functor.flip.obj A

def tensor (M : ExtrSheafProd.{u} Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrSheafProd.{u} Ab.{u+1} :=
{ val := tensor_presheaf M.val A,
  cond := begin
    introsI α _ X, dsimp [tensor_presheaf, AddCommGroup.tensor_functor],
    let e := _, change is_iso e,
    have hq := M.cond _ X, dsimp at hq, let q := _, change is_iso q at hq,
    have he : e = AddCommGroup.map_tensor q (𝟙 _) ≫
      AddCommGroup.tensor_pi_comparison _ _,
    { ext1 j,
      dsimp [AddCommGroup.tensor_pi_comparison],
      simp only [←AddCommGroup.map_tensor_comp_left, limits.limit.lift_π,
        limits.fan.mk_π_app, category.assoc]},
    rw he, resetI, apply_with is_iso.comp_is_iso { instances := ff },
    swap, apply_instance,
    use AddCommGroup.map_tensor (inv q) (𝟙 _),
    split,
    { rw [← AddCommGroup.map_tensor_comp_left, is_iso.hom_inv_id, AddCommGroup.map_tensor_id], },
    { rw [← AddCommGroup.map_tensor_comp_left, is_iso.inv_hom_id, AddCommGroup.map_tensor_id], },
  end } -- tensor products commutes with direct sums.

-- Slow, so probably break into pieces
def tensor_functor : ExtrSheafProd.{u} Ab.{u+1} ⥤ Ab.{u+1} ⥤ ExtrSheafProd.{u} Ab.{u+1} :=
{ obj := λ M,
  { obj := λ A, tensor M A,
    map := λ A B f,
      ⟨{ app := λ S, AddCommGroup.map_tensor (𝟙 _) f,
         naturality' := λ M N g, begin
          dsimp [tensor, tensor_presheaf, AddCommGroup.tensor_functor],
          simp [← AddCommGroup.map_tensor_eq_comp, ← AddCommGroup.map_tensor_eq_comp'],
         end,
         }⟩,
    map_id' := begin
      intros A,
      ext S : 3,
      dsimp, simpa,
    end,
    map_comp' := begin
      intros A B C f g,
      ext S : 3,
      dsimp, simp,
    end },
  map := λ M N f,
  { app := λ A,
    ⟨{ app := λ S, AddCommGroup.map_tensor (f.val.app _) (𝟙 _),
       naturality' := begin
        intros S T e,
        dsimp [tensor, tensor_presheaf, AddCommGroup.tensor_functor],
        simp only [← AddCommGroup.map_tensor_comp_left, nat_trans.naturality],
       end }⟩,
    naturality' := begin
      intros A B g,
      ext S : 3,
      dsimp,
      simp [← AddCommGroup.map_tensor_eq_comp, ← AddCommGroup.map_tensor_eq_comp'],
    end },
  map_id' := begin
    intros X,
    ext : 5,
    dsimp,
    simpa,
  end,
  map_comp' := begin
    intros X Y Z f g,
    ext : 5,
    dsimp, simp,
  end }

.

@[simps]
instance hom_has_add {M N : ExtrSheafProd.{u} Ab.{u+1}} : has_add (M ⟶ N) :=
⟨λ f g, ⟨f.val + g.val⟩⟩

@[simps]
instance hom_has_zero {M N : ExtrSheafProd.{u} Ab.{u+1}} : has_zero (M ⟶ N) :=
⟨⟨0⟩⟩

@[simps]
instance hom_has_neg {M N : ExtrSheafProd.{u} Ab.{u+1}} : has_neg (M ⟶ N) :=
⟨λ f, ⟨-f.val⟩⟩

@[simps]
instance hom_has_sub {M N : ExtrSheafProd.{u} Ab.{u+1}} : has_sub (M ⟶ N) :=
⟨λ f g, ⟨f.val - g.val⟩⟩

instance preadditive : preadditive (ExtrSheafProd.{u} Ab.{u+1}) :=
{ hom_group := λ P Q,
  { add_assoc := λ f g h, by { ext1, dsimp, rw add_assoc },
    zero_add := λ f, by { ext1, dsimp, rw zero_add },
    add_zero := λ f, by { ext1, dsimp, rw add_zero },
    nsmul := λ n f, ⟨n • f.val⟩,
    nsmul_zero' := λ f, by { ext1, dsimp, simp, },
    nsmul_succ' := λ n f, by { ext1, dsimp, exact succ_nsmul f.val n },
    sub_eq_add_neg := λ f g, by { ext1, dsimp, exact sub_eq_add_neg f.val g.val },
    zsmul := λ n f, ⟨n • f.val⟩,
    zsmul_zero' := λ f, by { ext1, dsimp, simp },
    zsmul_succ' := λ n f, by { ext1, dsimp, rw [add_zsmul, one_zsmul, add_comm], },
    zsmul_neg' := λ n f, by { ext1, dsimp, simpa, },
    add_left_neg := λ f, by { ext1, dsimp, simp },
    add_comm := λ f g, by { ext1, dsimp, rw add_comm },
    ..(infer_instance : has_add _),
    ..(infer_instance : has_neg _),
    ..(infer_instance : has_zero _),
    ..(infer_instance : has_sub _) },
  add_comp' := λ P Q R f f' g, by { ext1, dsimp, simp },
  comp_add' := λ P Q R f g g', by { ext1, dsimp, simp } }

def evaluation (S : ExtrDisc.{u}) :
  ExtrSheafProd.{u} Ab.{u+1} ⥤ Ab.{u+1} :=
ExtrSheafProd_to_presheaf _ ⋙ (evaluation _ _).obj (opposite.op S)

instance evaluation_additive (S) : functor.additive (evaluation S) :=
⟨λ M N f g, rfl⟩

def half_internal_hom (A : AddCommGroup.{u+1}) (M : ExtrSheafProd.{u} Ab.{u+1}) :
  ExtrSheafProd.{u} Ab.{u+1} :=
{ val :=
  { obj := λ S, AddCommGroup.of (A ⟶ M.val.obj S),
    map := λ X Y f, (preadditive_yoneda.flip.obj (opposite.op A)).map $ M.val.map f,
    map_id' := begin
      intros S,
      dsimp, simpa,
    end,
    map_comp' := begin
      intros R S T f g,
      dsimp,
      simp,
    end },
  cond := begin
    introsI α _ X, dsimp,
    let t := _, change is_iso t,
    have := M.cond α X, dsimp at this, let e := _, change is_iso e at this, resetI,
    let q : AddCommGroup.of (A ⟶ M.val.obj (opposite.op (ExtrDisc.sigma X))) ≅
      AddCommGroup.of (A ⟶ (∏ (λ i, M.val.obj (opposite.op (X i))))) :=
      (preadditive_yoneda.flip.obj (opposite.op A)).map_iso (as_iso e),
    let s : AddCommGroup.of (A ⟶ (∏ (λ i, M.val.obj (opposite.op (X i))))) ⟶
      ∏ (λ i, AddCommGroup.of (A ⟶ M.val.obj (opposite.op (X i)))) :=
      limits.pi.lift (λ i, (preadditive_yoneda.flip.obj (opposite.op A)).map
        (limits.pi.π _ i)),
    have ht : t = q.hom ≫ s,
    { dsimp [t, q, s, e], ext1,
      simp only [limits.limit.lift_π, limits.fan.mk_π_app, category.assoc],
      rw [← nat_trans.comp_app, ← functor.map_comp, limits.limit.lift_π],
      refl },
    rw ht, clear ht,
    suffices : is_iso s,
    { resetI, apply is_iso.comp_is_iso },
    -- Now we need to show that `Hom(A,(Π i, X i)) = Π i, Hom(A,X i)`.
    apply AddCommGroup.is_iso_hom_product_comparison.{u u+1},
  end }

def tensor_uncurry {A : AddCommGroup.{u+1}} {M N : ExtrSheafProd.{u} Ab.{u+1}}
  (e : M ⟶ half_internal_hom A N) :
  tensor M A ⟶ N := ExtrSheafProd.hom.mk $
{ app := λ S, AddCommGroup.tensor_uncurry $ e.val.app _,
  naturality' := begin
    intros X Y f,
    erw ← AddCommGroup.tensor_uncurry_curry,
    apply (AddCommGroup.tensor_curry_equiv _ _ _).injective,
    erw (AddCommGroup.tensor_curry_equiv _ _ _).apply_symm_apply,
    dsimp [AddCommGroup.tensor_curry_equiv],
    erw [AddCommGroup.tensor_curry_uncurry, ← nat_trans.naturality,
      ← AddCommGroup.tensor_curry_equiv_apply,
      ← AddCommGroup.tensor_curry_equiv_symm_apply,
      (AddCommGroup.tensor_curry_equiv _ _ _).apply_symm_apply],
  end }

def tensor_curry {A : AddCommGroup.{u+1}} {M N : ExtrSheafProd.{u} Ab.{u+1}}
  (e : M.tensor A ⟶ N) : M ⟶ half_internal_hom A N := ExtrSheafProd.hom.mk $
{ app := λ S, AddCommGroup.tensor_curry $ e.val.app _,
  naturality' := begin
    intros X Y f,
    dsimp [half_internal_hom],
    erw [← AddCommGroup.tensor_curry_uncurry],
    apply (AddCommGroup.tensor_curry_equiv _ _ _).symm.injective,
    simp_rw ← AddCommGroup.tensor_curry_equiv_apply,
    rw (AddCommGroup.tensor_curry_equiv _ _ _).symm_apply_apply,
    rw ← AddCommGroup.tensor_curry_equiv_symm_apply,
    rw (AddCommGroup.tensor_curry_equiv _ _ _).symm_apply_apply,
    dsimp,
    rw [AddCommGroup.tensor_uncurry_curry, ← nat_trans.naturality],
    refl,
  end }

end ExtrSheafProd

namespace condensed

/-- This is the functor that sends `A : Ab` to `M ⊗ A`,
where `M` is a condensed abelian group, functorial in both `M` and `A`. -/
def tensor_functor : Condensed.{u} Ab.{u+1} ⥤ Ab.{u+1} ⥤ Condensed.{u} Ab.{u+1} :=
(Condensed_ExtrSheafProd_equiv Ab.{u+1}).functor ⋙
((whiskering_right _ _ _).obj $ ((whiskering_right _ _ _).obj
  (Condensed_ExtrSheafProd_equiv Ab.{u+1}).inverse)).obj
  ExtrSheafProd.tensor_functor

/-- This is the tensor product of a condensed abelian group `M` and `A : Ab`. -/
def tensor (M : Condensed.{u} Ab.{u+1}) (A : Ab.{u+1}) : Condensed.{u} Ab.{u+1} :=
(tensor_functor.obj M).obj A

/-- Restrincting to `ExtrDisc` works as expeceted. -/
def tensor_functor_conj_iso :
  (Condensed_ExtrSheafProd_equiv Ab.{u+1}).inverse ⋙
  ((whiskering_right _ _ _).obj $ ((whiskering_right _ _ _).obj
    (Condensed_ExtrSheafProd_equiv Ab.{u+1}).functor)).obj tensor_functor ≅
  ExtrSheafProd.tensor_functor :=
nat_iso.of_components
(λ X, begin
  refine functor.associator _ _ _ ≪≫ _,
  refine iso_whisker_left _ (Condensed_ExtrSheafProd_equiv Ab.{u+1}).counit_iso ≪≫ _,
  refine functor.right_unitor _ ≪≫ _,
  refine functor.map_iso _ _,
  exact ((Condensed_ExtrSheafProd_equiv Ab.{u+1}).counit_iso.app X),
end)
begin
  intros X Y f, ext : 2,
  dsimp [tensor_functor],
  simp only [equivalence.fun_inv_map, equivalence.equivalence_mk'_counit,
    equivalence.equivalence_mk'_counit_inv, functor.map_comp, nat_trans.comp_app,
    category.assoc, iso.inv_hom_id_app_assoc, category.id_comp,
    nat_iso.cancel_nat_iso_hom_left],
  rw [← nat_trans.comp_app, ← functor.map_comp, ← nat_trans.comp_app],
  have : (Condensed_ExtrSheafProd_equiv Ab).counit_iso.inv.app Y ≫
    (Condensed_ExtrSheafProd_equiv Ab).counit_iso.hom.app Y = 𝟙 _,
  { rw [← nat_trans.comp_app, iso.inv_hom_id], refl },
  rw this,
  simp only [nat_trans.comp_app],
  dsimp,
  simp only [category_theory.functor.map_id, nat_trans.id_app, category.comp_id],
end

def tensor_functor_conj_iso' :
  tensor_functor ⋙ (whiskering_right _ _ _).obj
  (Condensed_ExtrSheafProd_equiv _).functor ≅
  (Condensed_ExtrSheafProd_equiv _).functor ⋙ ExtrSheafProd.tensor_functor :=
nat_iso.of_components
(λ X, begin
  dsimp [tensor_functor],
  refine functor.associator _ _ _ ≪≫ _,
  refine _ ≪≫ functor.right_unitor _,
  refine ((whiskering_left _ _ _).obj _).map_iso _,
  refine (Condensed_ExtrSheafProd_equiv _).counit_iso,
end)
begin
  intros X Y f, ext : 2,
  dsimp [tensor_functor],
  simp, dsimp, simp,
end

/-- The tensor product behaves in the naive way when evaluated
on extremally disconnected sets. -/
def tensor_eval_iso
  (M : Condensed.{u} Ab.{u+1}) (A : Ab.{u+1}) (S : ExtrDisc.{u}) :
  (tensor M A).val.obj (opposite.op S.val) ≅
  AddCommGroup.of (M.val.obj (opposite.op S.val) ⊗[ℤ] A) :=
let e := (tensor_functor_conj_iso'.app M).app A,
  e' := (ExtrSheafProd_to_presheaf _).map_iso e in
e'.app (opposite.op S)

/-- A variant of the tensor product functor for the endormophism category. -/
def endo_tensor :
  (endomorphisms $ Condensed.{u} Ab.{u+1}) ⥤ Ab.{u+1} ⥤
  (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
functor.flip $
{ obj := λ A, (tensor_functor.flip.obj A).map_endomorphisms,
  map := λ A B f, nat_trans.map_endomorphisms $ tensor_functor.flip.map f }

end condensed
