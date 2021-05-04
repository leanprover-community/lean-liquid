import for_mathlib.cech.basic
import for_mathlib.simplicial.complex
import for_mathlib.simplicial.augmented
import for_mathlib.Profinite.basic
import locally_constant.Vhat
import locally_constant.NormedGroup

noncomputable theory

open opposite category_theory

universe u
variables {X B : Profinite.{u}} (f : X ⟶ B) (M : NormedGroup.{u})

abbreviation cech_nerve := category_theory.cech_obj f

abbreviation cech_conerve : cosimplicial_object NormedGroup :=
(cech_nerve f).right_op ⋙ (NormedGroup.LCC.obj M)

abbreviation cech_complex : cochain_complex ℕ NormedGroup :=
(cech_conerve f M).to_cocomplex

abbreviation augmentation : cosimplicial_object.const.obj (op B) ⟶
  (cech_nerve f).right_op :=
let A := cech.augmentation_obj f in
{ app := λ i, (A.app (op i)).op,
  naturality' := sorry }

abbreviation augmentation' :
  cosimplicial_object.const.obj (op B) ⋙ (NormedGroup.LCC.obj M) ⟶ cech_conerve f M :=
whisker_right (augmentation f) _

variable (B)
def move_me : cosimplicial_object.const.obj ((NormedGroup.LCC.obj M).obj (op B)) ⟶
  cosimplicial_object.const.obj (op B) ⋙ (NormedGroup.LCC.obj M) :=
{ app := λ i, 𝟙 _ }
variable {B}

abbreviation augmentation'' :
  cosimplicial_object.const.obj ((NormedGroup.LCC.obj M).obj (op B)) ⟶ cech_conerve f M :=
(move_me B M) ≫ augmentation' f M

-- TODO: This must be somewhere...
instance : limits.has_zero_object NormedGroup :=
{ zero := 0,
  unique_to := sorry,
  unique_from := sorry }

abbreviation augmentation''' : cochain_complex.const.obj ((NormedGroup.LCC.obj M).obj (op B))
  ⟶ (cech_complex f M) := cosimplicial_object.augmentation' (augmentation'' _ _)

abbreviation main_cochain_complex : cochain_complex ℕ NormedGroup :=
  cochain_complex.shift_and_attach (augmentation''' f M)

theorem prop_819
  (surj : function.surjective f) (n : ℕ) (g : (main_cochain_complex f M).X (n+1))
  (hf : (main_cochain_complex f M).d (n+1) (n+2) g = 0) (c : ℝ) (hc : ∥ g ∥ ≤ c)
  (ε : ℝ) (hε : 0 < ε) : ∃ gg : (main_cochain_complex f M).X n,
  ∥ g ∥ ≤ (1+ε) * ∥ g ∥ ∧ (main_cochain_complex f M).d n (n+1) gg = g := sorry
