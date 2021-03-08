import category_theory.graded_object
import category_theory.preadditive
import data.int.basic

open category_theory category_theory.limits

class has_succ (α : Type*) := (succ : α → α)

-- fix this to something better?
notation `Ş` := has_succ.succ

-- do we want this for every semiring??
instance : has_succ ℕ := ⟨λ n, n + 1⟩
instance : has_succ ℤ := ⟨λ n, n + 1⟩

@[ext]
structure differential_object (ι : Type) (S₀ S₁ : ι → ι) (V : Type*)
  [category V] [has_zero_morphisms V] :=
(X : ι → V)
(differential : Π i, X (S₀ i) ⟶ X (S₁ i))
(differential2 : ∀ i j (h : S₁ i = S₀ j),
  differential i ≫ eq_to_hom (show X (S₁ i) = X (S₀ j), by rw h) ≫ differential j = 0)

variables (ι : Type) (S₀ S₁ : ι → ι) (V : Type*) {cov : bool}

namespace differential_object
variables [category V] [has_zero_morphisms V]

variables (C C₁ C₂ C₃ : differential_object ι S₀ S₁ V)

section category
-- technically, this can probably done in the generality of `differential_object`

variables {ι S₀ S₁ V}

@[ext]
structure hom :=
(f (i : ι) : C₁.X i ⟶ C₂.X i)
(comm' (i : ι) : C₁.differential i ≫ f (S₁ i) = f (S₀ i) ≫ C₂.differential i)

attribute [reassoc] hom.comm'

variables {C₁ C₂ C₃}

protected def id : hom C C :=
{ f := λ i, 𝟙 _,
  comm' := by { intros, simp only [category.id_comp, category.comp_id] } }

def comp (f : hom C₁ C₂) (g : hom C₂ C₃) : hom C₁ C₃ :=
{ f := λ i, f.f i ≫ g.f i,
  comm' := λ i, by { rw [hom.comm'_assoc, hom.comm', category.assoc] } }

instance : category (differential_object ι S₀ S₁ V) :=
{ hom := hom,
  id := differential_object.id,
  comp := λ _ _ _, comp,
  id_comp' := by { intros, ext, exact category.id_comp _ },
  comp_id' := by { intros, ext, exact category.comp_id _ },
  assoc' := by { intros, ext, dsimp [id, comp], rw [category.assoc] } }

@[simp] lemma id_f (i : ι) : (𝟙 C : C ⟶ C).f i = 𝟙 (C.X i) := rfl

@[simp] lemma comp_f (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  (f ≫ g).f i = f.f i ≫ g.f i := rfl

@[simp, reassoc]
lemma eq_to_hom_f (f : C₁ ⟶ C₂) (i j : ι) (h : i = j) :
  eq_to_hom (congr_arg _ h) ≫ f.f j = f.f i ≫ eq_to_hom (congr_arg _ h) :=
by { cases h, simp only [eq_to_hom_refl, category.id_comp, category.comp_id] }

@[simp, reassoc]
lemma eq_to_hom_differential (i j : ι) (h : i = j) :
  eq_to_hom (congr_arg _ h) ≫ C.differential j =
    C.differential i ≫ eq_to_hom (congr_arg _ $ by rw h) :=
by { cases h, simp only [eq_to_hom_refl, category.id_comp, category.comp_id] }

@[simps]
def iso_app (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
{ hom := f.hom.f i,
  inv := f.inv.f i,
  hom_inv_id' := by { rw [← comp_f, f.hom_inv_id, id_f] },
  inv_hom_id' := by { rw [← comp_f, f.inv_hom_id, id_f] } }

@[simps]
def iso_of_components (f : Π i, C₁.X i ≅ C₂.X i)
  (hf : ∀ i, C₁.differential i ≫ (f _).hom = (f _).hom ≫ C₂.differential i) :
  C₁ ≅ C₂ :=
{ hom :=
  { f := λ i, (f i).hom,
    comm' := hf },
  inv :=
  { f := λ i, (f i).inv,
    comm' := λ i,
    calc C₂.differential i ≫ (f (S₁ i)).inv
        = (f (S₀ i)).inv ≫ ((f (S₀ i)).hom ≫ C₂.differential i) ≫ (f (S₁ i)).inv : by simp
    ... = (f (S₀ i)).inv ≫ (C₁.differential i ≫ (f (S₁ i)).hom) ≫ (f (S₁ i)).inv : by rw hf
    ... = (f (S₀ i)).inv ≫ C₁.differential i : by simp },
  hom_inv_id' := by { ext i, exact (f i).hom_inv_id },
  inv_hom_id' := by { ext i, exact (f i).inv_hom_id } }

instance : has_zero_morphisms (differential_object ι S₀ S₁ V) :=
{ has_zero := λ C₁ C₂, ⟨{ f := λ i, 0, comm' := λ _, by simp only [zero_comp, comp_zero] }⟩,
  comp_zero' := by { intros, ext, rw [comp_f, comp_zero] },
  zero_comp' := by { intros, ext, rw [comp_f, zero_comp] } }

variables (ι V)

@[simps]
def forget : differential_object ι S₀ S₁ V ⥤ graded_object ι V :=
{ obj := λ C, C.X,
  map := λ _ _ f, f.f }

end category

end differential_object

namespace category_theory

variables {ι} {S₀ S₁} {V₁ V₂ : Type*}
variables [category V₁] [category V₂] [has_zero_morphisms V₁] [has_zero_morphisms V₂]

@[simps]
def functor.map_differential_object (F : V₁ ⥤ V₂)
  (hF : ∀ (x y : V₁), F.map (0 : x ⟶ y) = 0) :
  differential_object ι S₀ S₁ V₁ ⥤ differential_object ι S₀ S₁ V₂ :=
{ obj := λ C,
  { X := λ i, F.obj (C.X i),
    differential := λ i, F.map (C.differential i),
    differential2 := λ i j h,
    begin
      have aux := hF (C.X (S₀ i)) (C.X (S₁ j)),
      rw ← C.differential2 i j h at aux,
      simpa using aux,
    end },
  map := λ C₁ C₂ f,
  { f := λ i, F.map (f.f i),
    comm' := λ i, by simp only [← F.map_comp, f.comm'] },
  map_id' := by { intros, ext, exact F.map_id _ },
  map_comp' := by { intros, ext, exact F.map_comp _ _ } }

end category_theory

namespace differential_object

variables {ι V}
variables [has_succ ι] [category V] [has_zero_morphisms V]

local notation `differential_object'` cov :=
differential_object ι (bool.rec Ş id cov) (bool.rec id Ş cov) V

def coherent_indices : Π (cov : bool) (i j : ι), Prop
| ff i j := i = Ş j
| tt i j := Ş i = j

instance coherent_indices_decidable [decidable_eq ι] (cov : bool) (i j : ι) :
  decidable (coherent_indices cov i j) :=
by { cases cov; dsimp [coherent_indices]; apply_instance }

def d_aux (i j : ι) :
  Π (cov : bool) (C : differential_object' cov) (h : coherent_indices cov i j),
  C.X i ⟶ C.X j
| tt C h := C.differential i ≫ eq_to_hom (congr_arg C.X h)
| ff C h := eq_to_hom (congr_arg C.X h) ≫ C.differential j

variables [decidable_eq ι]

def d {cov : bool} (C : differential_object' cov) (i j : ι) : C.X i ⟶ C.X j :=
if h : coherent_indices cov i j then d_aux i j cov C h else 0

variables (C C₁ C₂ C₃ : differential_object' cov)

lemma d_eq_zero (i j : ι) (h : ¬ coherent_indices cov i j) : C.d i j = 0 :=
dif_neg h

@[simp]
lemma d_comp_d (i j k : ι) : C.d i j ≫ C.d j k = 0 :=
begin
  cases cov; dsimp [d]; split_ifs with h1 h2,
  any_goals { simp only [zero_comp, comp_zero] },
  all_goals { cases h1, cases h2, simpa [d_aux] using C.differential2 _ _ rfl }
end

variables {C₁ C₂ C₃}

@[reassoc]
lemma hom.comm (f : C₁ ⟶ C₂) (i j : ι) :
  C₁.d i j ≫ f.f j = f.f i ≫ C₂.d i j :=
begin
  cases cov; dsimp [d]; split_ifs with h,
  any_goals { simp only [zero_comp, comp_zero] },
  all_goals { cases h, simpa [d_aux] using f.comm' _ }
end

end differential_object

section special_cases

variables [has_succ ι] [category V] [has_zero_morphisms V]

local notation `differential_object'` cov :=
differential_object ι (bool.rec Ş id cov) (bool.rec id Ş cov) V

abbreviation chain_complex := differential_object' ff

abbreviation cochain_complex := differential_object' tt

variables {ι V} [decidable_eq ι]

namespace chain_complex

variables (C : chain_complex ι V) (i j k : ι)

def d : C.X i ⟶ C.X j := @differential_object.d ι V _ _ _ _ ff C i j

lemma d_eq_zero (i j : ι) (h : i ≠ Ş j) : C.d i j = 0 :=
differential_object.d_eq_zero _ _ _ h

@[simp] lemma d_comp_d : C.d i j ≫ C.d j k = 0 :=
differential_object.d_comp_d _ _ _ _

@[reassoc]
lemma hom.comm {C₁ C₂ : chain_complex ι V} (f : C₁ ⟶ C₂) (i j : ι) :
  C₁.d i j ≫ f.f j = f.f i ≫ C₂.d i j :=
differential_object.hom.comm f i j

end chain_complex

namespace cochain_complex

variables (C : cochain_complex ι V) (i j k : ι)

def d : C.X i ⟶ C.X j := @differential_object.d ι V _ _ _ _ tt C i j

lemma d_eq_zero (i j : ι) (h : Ş i ≠ j) : C.d i j = 0 :=
differential_object.d_eq_zero _ _ _ h

@[simp] lemma d_comp_d : C.d i j ≫ C.d j k = 0 :=
differential_object.d_comp_d _ _ _ _

@[reassoc]
lemma hom.comm {C₁ C₂ : cochain_complex ι V} (f : C₁ ⟶ C₂) (i j : ι) :
  C₁.d i j ≫ f.f j = f.f i ≫ C₂.d i j :=
differential_object.hom.comm f i j

end cochain_complex

end special_cases

namespace differential_object

variables {ι V} [has_succ ι] [category V] [preadditive V]

open category_theory.preadditive

section general

local notation `differential_object'` cov :=
differential_object ι (bool.rec Ş id cov) (bool.rec id Ş cov) V

def shift_differential : Π {cov : bool} (C : differential_object' cov) (i : ι),
  C.X (Ş (bool.rec Ş id cov i)) ⟶ C.X (Ş (bool.rec id Ş cov i))
| ff C i := -C.differential (Ş i)
| tt C i := -C.differential (Ş i)

@[simps]
def shift : (differential_object' cov) ⥤ differential_object' cov :=
{ obj := λ C,
  { X := λ i, C.X (Ş i),
    differential := shift_differential C,
    differential2 := λ i j h,
    begin
      cases cov; cases h; dsimp only [shift_differential];
      simp only [neg_comp, comp_neg, neg_neg];
      apply C.differential2; refl
    end },
  map := λ C₁ C₂ f,
  { f := λ i, f.f (Ş i),
    comm' := λ i,
    begin
      cases cov; dsimp only [shift_differential];
      simp only [neg_comp, comp_neg, neg_inj];
      exact f.comm' (Ş i)
    end } }

end general

section int

local notation `differential_object'` cov :=
differential_object ℤ (bool.rec Ş id cov) (bool.rec id Ş cov) V

def antishift_differential : Π {cov : bool} (C : (differential_object' cov)) (i : ℤ),
  C.X ((bool.rec Ş id cov i) - 1) ⟶ C.X ((bool.rec id Ş cov i) - 1)
| ff C i := -eq_to_hom (congr_arg _ (sub_add_eq_add_sub i 1 1).symm) ≫ C.differential (i-1)
| tt C i := -C.differential (i-1) ≫ eq_to_hom (congr_arg _ $ sub_add_eq_add_sub i 1 1)

@[simps]
def antishift : (differential_object' cov) ⥤ differential_object' cov :=
{ obj := λ C,
  { X := λ i, C.X (i-1),
    differential := antishift_differential C,
    differential2 := λ i j h,
    begin
      cases cov; cases h; dsimp [antishift_differential];
      simp only [category.id_comp, category.comp_id, comp_neg, neg_comp, neg_neg, eq_to_hom_refl],
      { slice_lhs 2 4 { erw C.differential2 (j+1-1) (j-1) (sub_add_eq_add_sub j 1 1).symm },
        rw comp_zero },
      { slice_lhs 1 3 { erw C.differential2 (i-1) (i+1-1) (sub_add_eq_add_sub i 1 1) },
        rw zero_comp }
    end },
  map := λ C₁ C₂ f,
  { f := λ i, f.f (i-1),
    comm' := λ i,
    begin
      cases cov; dsimp [antishift_differential];
      simp only [neg_comp, comp_neg, neg_inj],
      { erw [category.assoc, f.comm' (i-1), eq_to_hom_f_assoc],
        exact (sub_add_eq_add_sub i 1 1).symm },
      { erw [← f.comm'_assoc (i-1), category.assoc, eq_to_hom_f], refl,
        exact (sub_add_eq_add_sub i 1 1), },
    end } }

instance : has_shift (differential_object ℤ (bool.rec Ş id cov) (bool.rec id Ş cov) V) :=
{ shift :=
  { functor := shift,
    inverse := antishift,
    unit_iso := nat_iso.of_components
      (λ C, iso_of_components
        (λ i, eq_to_iso $ congr_arg _ (sub_add_cancel i 1).symm)
        (λ i,
        begin
          cases cov; dsimp [shift_differential, antishift_differential];
          simp only [neg_comp, comp_neg, neg_neg, eq_to_hom_trans_assoc],
          { erw [eq_to_hom_differential], refl, exact (sub_add_cancel i 1).symm },
          { erw [← category.assoc, eq_to_hom_differential, category.assoc, eq_to_hom_trans] }
        end))
      (λ C₁ C₂ f, by { ext i, dsimp, rw eq_to_hom_f }),
    counit_iso := nat_iso.of_components
      (λ C, iso_of_components
        (λ i, eq_to_iso $ show C.X (i+1-1) = C.X i, from congr_arg _ (add_sub_cancel i 1))
        (λ i,
        begin
          cases cov; dsimp [shift_differential, antishift_differential];
          simp only [neg_comp, comp_neg, neg_neg, eq_to_hom_trans_assoc],
          { erw [category.assoc, ← eq_to_hom_differential, eq_to_hom_trans_assoc],
            refl, exact add_sub_cancel i 1 },
          { erw [category.assoc, eq_to_hom_trans, eq_to_hom_differential], refl }
        end))
      (λ C₁ C₂ f, by { ext i, dsimp, rw ← eq_to_hom_f }),
    functor_unit_iso_comp' :=
    by { intros, ext i, dsimp, simp only [eq_to_hom_refl, eq_to_hom_trans] } } }

end int

end differential_object

namespace chain_complex

variables {V} [category V] [preadditive V]

instance : has_shift (chain_complex ℤ V) :=
@differential_object.category_theory.has_shift V ff _ _

end chain_complex

namespace cochain_complex

variables {V} [category V] [preadditive V]

instance : has_shift (cochain_complex ℤ V) :=
@differential_object.category_theory.has_shift V tt _ _

end cochain_complex
