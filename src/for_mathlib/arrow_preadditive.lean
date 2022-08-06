import category_theory.preadditive
import category_theory.arrow


-- TODO : generalize to comma categories?

namespace category_theory

variables {A : Type*} [category A] [preadditive A]

local attribute [simp] preadditive.comp_nsmul preadditive.nsmul_comp
    preadditive.comp_zsmul preadditive.zsmul_comp

instance arrow.has_zero (P Q : arrow A) : has_zero (P ⟶ Q) :=
⟨arrow.hom_mk (show 0 ≫ Q.hom = P.hom ≫ 0, by simp)⟩
instance arrow.has_add (P Q : arrow A) : has_add (P ⟶ Q) :=
⟨λ f g, arrow.hom_mk (show (f.left + g.left) ≫ Q.hom = P.hom ≫ (f.right + g.right), by simp)⟩
instance arrow.has_neg (P Q : arrow A) : has_neg (P ⟶ Q) :=
⟨λ f, arrow.hom_mk (show (-f.left) ≫ Q.hom = P.hom ≫ (-f.right), by simp)⟩
instance arrow.has_sub (P Q : arrow A) : has_sub (P ⟶ Q) :=
⟨λ f g, arrow.hom_mk (show (f.left - g.left) ≫ Q.hom = P.hom ≫ (f.right - g.right), by simp)⟩
instance arrow.has_nsmul (P Q : arrow A) : has_smul ℕ (P ⟶ Q) :=
⟨λ n f, arrow.hom_mk (show (n • f.left) ≫ Q.hom = P.hom ≫ (n • f.right), by simp)⟩
instance arrow.has_zsmul (P Q : arrow A) : has_smul ℤ (P ⟶ Q) :=
⟨λ n f, arrow.hom_mk (show (n • f.left) ≫ Q.hom = P.hom ≫ (n • f.right), by simp)⟩
.
@[simp] lemma arrow.has_add_left {P Q : arrow A} (f g : P ⟶ Q) :
  (f + g).left = f.left + g.left := rfl
@[simp] lemma arrow.has_add_right {P Q : arrow A} (f g : P ⟶ Q) :
  (f + g).right = f.right + g.right := rfl
@[simp] lemma arrow.has_neg_left {P Q : arrow A} (f : P ⟶ Q) :
  (-f).left = -(f.left) := rfl
@[simp] lemma arrow.has_neg_right {P Q : arrow A} (f : P ⟶ Q) :
  (-f).right = -(f.right) := rfl
@[simp] lemma arrow.has_sub_left {P Q : arrow A} (f g : P ⟶ Q) :
  (f - g).left = f.left - g.left := rfl
@[simp] lemma arrow.has_sub_right {P Q : arrow A} (f g : P ⟶ Q) :
  (f - g).right = f.right - g.right := rfl

instance arrow.add_comm_group (P Q : arrow A) : add_comm_group (P ⟶ Q) :=
{ add_assoc := λ f g h, by ext; apply add_assoc,
  zero_add := λ f, by ext; apply zero_add,
  add_zero := λ f, by ext; apply add_zero,
  add_left_neg := λ f, by ext; apply add_left_neg,
  add_comm := λ f g, by ext; apply add_comm,
  ..arrow.has_add P Q,
  ..arrow.has_zero P Q,
  ..arrow.has_neg P Q,
  ..arrow.has_nsmul P Q,
  ..arrow.has_zsmul P Q }
.
instance arrow.preadditive : preadditive (arrow A) :=
⟨infer_instance, by { introv P, ext; apply preadditive.add_comp },
  by { introv P, ext; apply preadditive.comp_add }⟩



end category_theory
