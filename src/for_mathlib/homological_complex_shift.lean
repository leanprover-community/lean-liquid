import category_theory.shift
import algebra.homology.homological_complex
import algebra.homology.homotopy_category
import data.int.parity
import tactic.ring
import for_mathlib.homology_iso
import category_theory.arrow
import category_theory.preadditive

local attribute [simp] category_theory.preadditive.zsmul_comp category_theory.preadditive.comp_zsmul

-- move this section
namespace int

def neg_one_pow (n : ℤ) : ℤ := @has_pow.pow (units ℤ) ℤ _ (-1) n

@[simp] lemma neg_one_pow_add (n m : ℤ) : neg_one_pow (n + m) = neg_one_pow n * neg_one_pow m :=
by { delta neg_one_pow, rw zpow_add, simp }

@[simp] lemma neg_one_pow_one : neg_one_pow 1 = -1 := rfl

-- This lemma is provable by `neg_one_pow_neg`, but it is nice to have a rfl-lemma for this.
-- The priority is thus higher to silence the linter.
@[simp, priority 1100] lemma neg_one_pow_neg_one : neg_one_pow (-1) = -1 := rfl

@[simp] lemma neg_one_pow_neg_zero : neg_one_pow 0 = 1 := rfl

lemma neg_one_pow_ite (n : ℤ) : neg_one_pow n = if even n then 1 else -1 :=
begin
  induction n using int.induction_on with n h n h,
  { simp [neg_one_pow] },
  { simp [h, apply_ite has_neg.neg] with parity_simps },
  { rw [sub_eq_add_neg, neg_one_pow_add],
    simp [h, apply_ite has_neg.neg] with parity_simps }
end

lemma neg_one_pow_even {n : ℤ} (h : even n) : neg_one_pow n = 1 :=
by rw [neg_one_pow_ite, if_pos h]

lemma neg_one_pow_odd {n : ℤ} (h : odd n) : neg_one_pow n = -1 :=
by rw [neg_one_pow_ite, if_neg (odd_iff_not_even.mp h)]

@[simp] lemma neg_one_pow_bit0 (n : ℤ) : neg_one_pow (bit0 n) = 1 :=
neg_one_pow_even (even_bit0 n)

@[simp] lemma neg_one_pow_bit1 (n : ℤ) : neg_one_pow (bit1 n) = -1 :=
neg_one_pow_odd (odd_bit1 n)

lemma neg_one_pow_eq_pow_abs (n : ℤ) : neg_one_pow n = (-1) ^ n.nat_abs :=
begin
  rw neg_one_pow_ite,
  convert (neg_one_pow_ite n.nat_abs).symm using 2,
  { simp with parity_simps },
  { delta neg_one_pow, simp }
end

lemma neg_one_pow_eq_neg_one_npow (n : ℕ) : neg_one_pow n = (-1) ^ n :=
by { delta neg_one_pow, simp }

@[simp] lemma neg_one_pow_neg (n : ℤ) : neg_one_pow (-n) = neg_one_pow n :=
by simp [neg_one_pow_ite] with parity_simps

@[simp] lemma neg_one_pow_sub (n m : ℤ) : neg_one_pow (n - m) = neg_one_pow n * neg_one_pow m :=
by rw [sub_eq_neg_add, neg_one_pow_add, neg_one_pow_neg, mul_comm]

@[simp] lemma neg_one_pow_mul_self (n : ℤ) : neg_one_pow n * neg_one_pow n = 1 :=
by { delta neg_one_pow, simp }

@[simp] lemma neg_one_pow_smul_self {α : Type*} [add_comm_group α] (n : ℤ) (X : α) :
  neg_one_pow n • neg_one_pow n • X = X :=
by simp [smul_smul]

open category_theory

variables {A : Type*} [category A] [preadditive A]

@[simps]
def neg_one_pow_smul_iso (n : ℤ) {X Y : A} (e : X ≅ Y) : X ≅ Y :=
{ hom := n.neg_one_pow • e.hom,
  inv := n.neg_one_pow • e.inv }

@[simps]
def neg_one_pow_arrow_iso_left (n : ℤ) {X Y : A} (f : X ⟶ Y) :
  arrow.mk f ≅ arrow.mk (n.neg_one_pow • f) :=
arrow.iso_mk (n.neg_one_pow_smul_iso (iso.refl _)) (iso.refl _) (by { dsimp, simp })

@[simps]
def neg_one_pow_arrow_iso_right (n : ℤ) {X Y : A} (f : X ⟶ Y) :
  arrow.mk f ≅ arrow.mk (n.neg_one_pow • f) :=
arrow.iso_mk (iso.refl _) (n.neg_one_pow_smul_iso (iso.refl _)) (by { dsimp, simp })

end int

universes v u

open category_theory category_theory.limits category_theory.preadditive

variables (V : Type u) [category.{v} V] [preadditive V]

namespace homological_complex

lemma complex_shape.up'_add_right_cancel {α : Type*} [add_cancel_comm_monoid α] (a : α)
  {i j} (k : α) : (complex_shape.up' a).rel (i+k) (j+k) ↔ (complex_shape.up' a).rel i j :=
by { dsimp, rw [add_assoc, add_comm k a, ← add_assoc], exact add_left_inj _ }

lemma complex_shape.up_add_right_cancel {α : Type*} [add_cancel_comm_monoid α] [has_one α]
  {i j} (k : α) : (complex_shape.up α).rel (i+k) (j+k) ↔ (complex_shape.up α).rel i j :=
complex_shape.up'_add_right_cancel 1 k

@[simps]
def shift_functor (n : ℤ) : cochain_complex V ℤ ⥤ cochain_complex V ℤ :=
{ obj := λ X,
  { X := λ i, X.X (i + n),
    d := λ i j, n.neg_one_pow • X.d _ _,
    shape' := λ i j h, by { rw [X.shape (i+n) (j+n), smul_zero],
      rwa complex_shape.up_add_right_cancel } },
  map := λ X Y f, { f := λ i, f.f _ } }

variables {V} {ι : Type*} {c : complex_shape ι}

def X_eq_to_iso (X : homological_complex V c) {i j : ι} (h : i = j) : X.X i ≅ X.X j :=
eq_to_iso $ congr_arg X.X h

@[simp]
lemma X_eq_to_iso_inv (X : homological_complex V c) {i j : ι} (h : i = j) :
  (X.X_eq_to_iso h).inv = (X.X_eq_to_iso h.symm).hom := rfl

@[simp, reassoc]
lemma X_eq_to_iso_d (X : homological_complex V c) {i j k : ι} (h : i = j) :
  (X.X_eq_to_iso h).hom ≫ X.d j k = X.d i k := by { subst h, exact category.id_comp _ }

@[simp, reassoc]
lemma X_d_eq_to_iso (X : homological_complex V c) {i j k : ι} (h : j = k) :
  X.d i j ≫ (X.X_eq_to_iso h).hom = X.d i k := by { subst h, exact category.comp_id _ }

@[simp, reassoc]
lemma X_eq_to_iso_trans (X : homological_complex V c) {i j k : ι} (h : i = j) (h' : j = k) :
  (X.X_eq_to_iso h).hom ≫ (X.X_eq_to_iso h').hom = (X.X_eq_to_iso (h.trans h')).hom :=
by { simp [X_eq_to_iso] }

@[simp]
lemma X_eq_to_iso_refl (X : homological_complex V c) {i : ι} :
  (X.X_eq_to_iso (refl i)).hom = 𝟙 _ := rfl

@[simp, reassoc]
lemma X_eq_to_iso_f {X Y : homological_complex V c} (f : X ⟶ Y) {i j : ι} (h : i = j) :
  (X.X_eq_to_iso h).hom ≫ f.f j = f.f i ≫ (Y.X_eq_to_iso h).hom :=
by { subst h, simp [X_eq_to_iso] }

variables (V)

instance : has_shift (cochain_complex V ℤ) ℤ :=
has_shift_mk _ _
{ F := shift_functor V,
  ε := nat_iso.of_components (λ X, hom.iso_of_components (λ i, X.X_eq_to_iso (add_zero _).symm)
    (λ i j r, by { dsimp, simp })) (λ X Y f, by { ext, dsimp, simp }),
  μ := λ n m, nat_iso.of_components (λ X, hom.iso_of_components
    (λ i, X.X_eq_to_iso (by rw [add_comm n m, add_assoc]))
    (λ i j r, by { dsimp, simp [smul_smul, mul_comm] })) (λ i j f, by { ext, dsimp, simp }),
  associativity := λ m₁ m₂ m₃ X, by { ext, dsimp, simp [X_eq_to_iso] },
  left_unitality := λ n X, by { ext, dsimp, simpa [X_eq_to_iso] },
  right_unitality := λ n X, by { ext, dsimp, simpa [X_eq_to_iso] } }

local attribute[instance] endofunctor_monoidal_category

@[simp] lemma shift_X (X : cochain_complex V ℤ) (n m : ℤ) :
  (X⟦n⟧).X m = X.X (m + n) := rfl

@[simp] lemma shift_d (X : cochain_complex V ℤ) (n i j : ℤ) :
  (X⟦n⟧).d i j = n.neg_one_pow • X.d (i + n) (j + n) := rfl

@[simp] lemma shift_f {X Y : cochain_complex V ℤ} (f : X ⟶ Y) (n i : ℤ) :
  (f⟦n⟧').f i = f.f (i + n) := rfl

instance (n : ℤ) : functor.additive ((shift_monoidal_functor (cochain_complex V ℤ) ℤ).obj n) := {}
instance shift_functor_additive (n : ℤ) : functor.additive (shift_functor V n) := {}

variable {V}

def homotopy_shift {X Y : cochain_complex V ℤ} {f g : X ⟶ Y} (h : homotopy f g) (n : ℤ)  :
  homotopy (f⟦n⟧') (g⟦n⟧') :=
{ hom := λ i j, n.neg_one_pow • h.hom _ _,
  zero' := λ i j r, by { rw ← complex_shape.up_add_right_cancel n at r, simp [h.zero _ _ r] },
  comm := λ i, begin
    dsimp,
    suffices : X.d (i + n) (i + n + 1) ≫ h.hom (i + n + 1) (i + n) +
      h.hom (i + n) (i + n - 1) ≫ Y.d (i + n - 1) (i + n) =
      X.d (i + n) (i + 1 + n) ≫ h.hom (i + 1 + n) (i + n) +
      h.hom (i + n) (i - 1 + n) ≫ Y.d (i - 1 + n) (i + n),
    { simpa [h.comm (i+n), d_next, prev_d, add_right_inj] },
    congr' 3; ring,
  end }

variable (V)

def homotopy_category.shift_functor (n : ℤ) :
  (homotopy_category V (complex_shape.up ℤ)) ⥤ (homotopy_category V (complex_shape.up ℤ)) :=
category_theory.quotient.lift _ (shift_functor _ n ⋙ homotopy_category.quotient _ _)
begin
  rintros X Y f g ⟨h⟩,
  apply homotopy_category.eq_of_homotopy,
  exact homotopy_shift h n,
end

def homotopy_category.shift_ε :
  𝟭 _ ≅ homotopy_category.shift_functor V 0 :=
begin
  refine nat_iso.of_components _ _,
  { rintro ⟨X⟩,
    refine (homotopy_category.quotient _ _).map_iso (hom.iso_of_components _ _),
    exact (λ i, X.X_eq_to_iso (add_zero _).symm),
    { introv, dsimp, simp } },
  { rintro ⟨X⟩ ⟨Y⟩ f, dsimp,
    rw ← homotopy_category.quotient_map_out f,
    erw quotient.lift_map_functor_map,
    simp only [functor.comp_map, ← functor.map_comp],
    congr' 1, ext, dsimp, simp }
end

def homotopy_category.shift_functor_add (n m : ℤ) :
  homotopy_category.shift_functor V n ⋙ homotopy_category.shift_functor V m ≅
    homotopy_category.shift_functor V (n + m) :=
begin
  refine nat_iso.of_components _ _,
  { rintro ⟨X⟩,
    refine (homotopy_category.quotient _ _).map_iso (hom.iso_of_components _ _),
    exact (λ i, X.X_eq_to_iso (by rw [add_comm n m, add_assoc])),
    { introv r, dsimp [homotopy_category.shift_functor], simp [smul_smul, mul_comm] } },
  { rintro ⟨X⟩ ⟨Y⟩ f, dsimp,
    rw ← homotopy_category.quotient_map_out f,
    erw quotient.lift_map_functor_map,
    conv_rhs { erw quotient.lift_map_functor_map },
    simp only [functor.comp_map, ← functor.map_comp],
    congr' 1, ext, dsimp, simp }
end

@[simp]
lemma homotopy_category.shift_functor_obj_as {X : cochain_complex V ℤ} (n : ℤ) :
  (homotopy_category.shift_functor V n).obj ⟨X⟩ = ⟨X⟦n⟧⟩ := rfl

@[simp]
lemma homotopy_category.shift_functor_map_quotient (n : ℤ) {X Y : cochain_complex V ℤ} (f : X ⟶ Y) :
  (homotopy_category.shift_functor V n).map ((homotopy_category.quotient V _).map f) =
  (homotopy_category.quotient V _).map (f⟦n⟧') := rfl

lemma quotient_eq_to_hom {X Y : homotopy_category V (complex_shape.up ℤ)} (h : X = Y) :
  eq_to_hom h = (homotopy_category.quotient V (complex_shape.up ℤ)).map (eq_to_hom (by rw h)) :=
by { subst h, simpa }

lemma homotopy_category.has_shift_associativity_aux :
  ∀ (m₁ m₂ m₃ : ℤ) (X : homotopy_category V (complex_shape.up ℤ)),
    (homotopy_category.shift_functor V m₃).map
          ((homotopy_category.shift_functor_add V m₁ m₂).hom.app X) ≫
        (homotopy_category.shift_functor_add V (m₁ + m₂) m₃).hom.app X ≫
          eq_to_hom (by rw add_assoc) =
      (homotopy_category.shift_functor_add V m₂ m₃).hom.app
          ((homotopy_category.shift_functor V m₁).obj X) ≫
        (homotopy_category.shift_functor_add V m₁ (m₂ + m₃)).hom.app X :=
λ m₁ m₂ m₃ ⟨X⟩, by { dsimp [homotopy_category.shift_functor_add],
  rw quotient_eq_to_hom, simp only [← functor.map_comp], congr' 1, ext, simp [X_eq_to_iso] }

lemma homotopy_category.has_shift_left_unitality_aux :
  ∀ (n : ℤ) (X : homotopy_category V (complex_shape.up ℤ)),
    (homotopy_category.shift_functor V n).map
          ((homotopy_category.shift_ε V).hom.app X) ≫
        (homotopy_category.shift_functor_add V 0 n).hom.app X =
      eq_to_hom (by { dsimp, rw zero_add }) :=
λ n ⟨X⟩, by { dsimp [homotopy_category.shift_ε,
  homotopy_category.shift_functor_add], rw quotient_eq_to_hom, simp only [← functor.map_comp],
  congr' 1, ext, simp [X_eq_to_iso] }

lemma homotopy_category.has_shift_right_unitality_aux :
  ∀ (n : ℤ) (X : homotopy_category V (complex_shape.up ℤ)),
    (homotopy_category.shift_ε V).hom.app
          ((homotopy_category.shift_functor V n).obj X) ≫
        (homotopy_category.shift_functor_add V n 0).hom.app X =
      eq_to_hom (by { dsimp, rw add_zero }) :=
λ n ⟨X⟩, by { dsimp [homotopy_category.shift_ε,
  homotopy_category.shift_functor_add], rw quotient_eq_to_hom, simp only [← functor.map_comp],
  congr' 1, ext, simp [X_eq_to_iso] }

instance homotopy_category.has_shift : has_shift (homotopy_category V (complex_shape.up ℤ)) ℤ :=
has_shift_mk _ _
{ F := homotopy_category.shift_functor V,
  ε := homotopy_category.shift_ε V,
  μ := homotopy_category.shift_functor_add V,
  associativity := homotopy_category.has_shift_associativity_aux _,
  left_unitality := homotopy_category.has_shift_left_unitality_aux _,
  right_unitality := homotopy_category.has_shift_right_unitality_aux _ }

@[simp] lemma homotopy_category.quotient_obj_shift (X : cochain_complex V ℤ) (n : ℤ) :
  ((homotopy_category.quotient V _).obj X)⟦n⟧ = ⟨X⟦n⟧⟩ := rfl

@[simp] lemma homotopy_category.shift_as (X : homotopy_category V (complex_shape.up ℤ)) (n : ℤ) :
  (X⟦n⟧).as = X.as⟦n⟧ := rfl

@[simp] lemma homotopy_category.quotient_map_shift {X Y : cochain_complex V ℤ} (f : X ⟶ Y) (n : ℤ) :
  ((homotopy_category.quotient V _).map f)⟦n⟧' = (homotopy_category.quotient V _).map (f⟦n⟧') := rfl

@[simp] lemma shift_ε_app (X : cochain_complex V ℤ) :
  (shift_monoidal_functor _ ℤ).ε.app ((homotopy_category.quotient _ _).obj X) =
    (homotopy_category.quotient _ _).map ((shift_monoidal_functor _ ℤ).ε.app X) := rfl

@[simp]
lemma shift_ε_inv_app (X : cochain_complex V ℤ) :
  (shift_monoidal_functor _ ℤ).ε_iso.inv.app ((homotopy_category.quotient _ _).obj X) =
    (homotopy_category.quotient _ _).map ((shift_monoidal_functor _ ℤ).ε_iso.inv.app X) :=
begin
  rw [← cancel_mono ((shift_monoidal_functor _ ℤ).ε.app ((homotopy_category.quotient _ _).obj X)),
    ε_inv_hom_app, shift_ε_app, ← functor.map_comp, ε_inv_hom_app],
  refl
end

@[simp] lemma shift_μ_app (i j : ℤ) (X : cochain_complex V ℤ) :
  ((shift_monoidal_functor _ ℤ).μ i j).app ((homotopy_category.quotient _ _).obj X) =
    (homotopy_category.quotient _ _).map (((shift_monoidal_functor _ ℤ).μ i j).app X) := rfl

@[simp]
lemma shift_μ_inv_app (i j : ℤ) (X : cochain_complex V ℤ) :
  ((shift_monoidal_functor _ ℤ).μ_iso i j).inv.app ((homotopy_category.quotient _ _).obj X) =
    (homotopy_category.quotient _ _).map (((shift_monoidal_functor _ ℤ).μ_iso i j).inv.app X) :=
begin
  rw [← cancel_mono (((shift_monoidal_functor _ ℤ).μ i j).app
      ((homotopy_category.quotient _ _).obj X)),
    μ_inv_hom_app, shift_μ_app, ← functor.map_comp, μ_inv_hom_app],
  refl
end
local attribute [reducible] discrete.add_monoidal

@[simp] lemma shift_μ_hom_app_f (A : cochain_complex V ℤ) (i j k : ℤ) :
  hom.f (((shift_monoidal_functor _ ℤ).μ i j).app A) k =
    (A.X_eq_to_iso $ by { dsimp, ring }).hom := rfl

@[simp] lemma shift_μ_inv_app_f (A : cochain_complex V ℤ) (i j k : ℤ) :
  hom.f (((shift_monoidal_functor _ ℤ).μ_iso i j).inv.app A) k =
    (A.X_eq_to_iso $ by { dsimp, ring }).hom :=
begin
  generalize_proofs h,
  rw ← cancel_epi (A.X_eq_to_iso h.symm).hom,
  conv_lhs { rw [← shift_μ_hom_app_f, ← comp_f] },
  simpa [-comp_f]
end

@[simp] lemma shift_ε_hom_app_f (A : cochain_complex V ℤ) (i : ℤ) :
  hom.f ((shift_monoidal_functor _ ℤ).ε.app A) i = (A.X_eq_to_iso $ by { dsimp, ring }).hom :=
rfl

@[simp]
lemma shift_ε_inv_app_f (A : cochain_complex V ℤ) (i : ℤ) :
  hom.f ((shift_monoidal_functor _ ℤ).ε_iso.inv.app A) i =
    (A.X_eq_to_iso $ by { dsimp, ring }).hom :=
begin
  haveI : epi (hom.f ((shift_monoidal_functor _ ℤ).ε.app A) i),
  { rw shift_ε_hom_app_f, apply_instance },
  rw [← cancel_epi (hom.f ((shift_monoidal_functor _ ℤ).ε.app A) i), ← comp_f,
    category_theory.ε_hom_inv_app, homological_complex.id_f],
  dsimp, simpa
end

open category_theory.abelian
variables {A : Type u} [category.{v} A] [abelian A]

noncomputable
def homology_shift_obj_iso (X : cochain_complex A ℤ) (i j : ℤ) :
  (homology_functor _ _ j).obj (X⟦i⟧) ≅ (homology_functor _ _ (j + i)).obj X :=
begin
  refine homology_iso _ (j-1) j (j+1) _ _ ≪≫ _ ≪≫
    (homology_iso _ (j - 1 + i) (j+i) (j+1+i) _ _).symm,
  { simp },
  { simp },
  { exact homology.map_iso _ _
      (int.neg_one_pow_arrow_iso_left _ _).symm (int.neg_one_pow_arrow_iso_right _ _).symm rfl },
  { dsimp, abel },
  { dsimp, abel },
end

@[simp, reassoc]
lemma homology.π'_ι {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  homology.π' f g w ≫ homology.ι f g w = kernel.ι g ≫ cokernel.π f :=
by { delta homology.π' homology.ι homology_iso_kernel_desc, simp }

@[simp, reassoc]
lemma homology.desc'_ι {X X' Y Z Z' : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
  (f' : X' ⟶ Y) (g' : Y ⟶ Z') (w' : f' ≫ g' = 0) (h₁) (h₂) (h₃) :
  homology.desc' _ _ w (kernel.lift _ (kernel.ι _) h₁ ≫ homology.π' _ _ _) h₂ ≫
  homology.ι _ _ w' = homology.ι _ _ _ ≫ cokernel.desc _ (cokernel.π _) h₃ :=
by { ext, simp, }

@[simp, reassoc]
lemma homology.π'_lift {X X' Y Z Z' : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
  (f' : X' ⟶ Y) (g' : Y ⟶ Z') (w' : f' ≫ g' = 0) (h₁) (h₂) (h₃) :
  homology.π' _ _ w ≫ homology.lift _ _ w' (homology.ι _ _ _ ≫
    cokernel.desc _ (cokernel.π _) h₁) h₂ =
  kernel.lift _ (kernel.ι _) h₃ ≫ homology.π' _ _ _ :=
by { ext, simp }

variable (A)

@[simp]
lemma shift_functor_eq (V : Type*) [category V] [preadditive V] (i) :
  homological_complex.shift_functor V i = category_theory.shift_functor _ i := rfl

noncomputable
def homology_shift_iso (i j : ℤ) :
  shift_functor _ i ⋙ homology_functor A (complex_shape.up ℤ) j ≅
    homology_functor A (complex_shape.up ℤ) (j + i) :=
nat_iso.of_components (λ X, homology_shift_obj_iso X i j : _)
begin
  intros X Y f,
  ext,
  dsimp [homology_shift_obj_iso, homology_iso, homology.map_iso],
  simp,
end

end homological_complex
