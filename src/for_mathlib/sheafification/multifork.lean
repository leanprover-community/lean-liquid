import category_theory.limits.shapes.products

namespace category_theory.limits

open category_theory

universes v u

variables {C : Type u} [category.{v} C]

inductive walking_multipair {α β : Type v} (fst snd : β → α) : Type v
| zero : α → walking_multipair
| one : β → walking_multipair

namespace walking_multipair

variables {α β : Type v} (fst snd : β → α)

inductive hom  : Π (A B : walking_multipair fst snd), Type v
| id (A)  : hom A A
| fst (b) : hom (zero (fst b)) (one b)
| snd (b) : hom (zero (snd b)) (one b)

def comp : Π {A B C : walking_multipair fst snd} (f : hom fst snd A B) (g : hom fst snd B C),
  hom fst snd A C
| _ _ _ (hom.id X) g := g
| _ _ _ (hom.fst b) (hom.id x) := hom.fst b
| _ _ _ (hom.snd b) (hom.id x) := hom.snd b

instance : small_category (walking_multipair fst snd) :=
{ hom := hom fst snd,
  id := hom.id,
  comp := λ X Y Z, comp fst snd,
  id_comp' := begin
    rintro (_|_) (_|_) (_|_|_),
    tidy
  end,
  comp_id' := begin
    rintro (_|_) (_|_) (_|_|_),
    tidy
  end,
  assoc' := begin
    rintro (_|_) (_|_) (_|_) (_|_) (_|_|_) (_|_|_) (_|_|_),
    tidy,
  end }

end walking_multipair

variables {α β : Type v} {fst snd : β → α}

def multipair (L : α → C) (R : β → C)
  (F : Π b, L (fst b) ⟶ R b) (S : Π b, L (snd b) ⟶ R b) :
  walking_multipair fst snd ⥤ C :=
{ obj := λ x,
  match x with
  | walking_multipair.zero a := L a
  | walking_multipair.one b := R b
  end,
  map := λ x y f,
  match x, y, f with
  | _, _, walking_multipair.hom.id x := 𝟙 _
  | _, _, walking_multipair.hom.fst b := F _
  | _, _, walking_multipair.hom.snd b := S _
  end,
  map_id' := begin
    rintros (_|_),
    tidy,
  end,
  map_comp' := begin
    rintros (_|_) (_|_) (_|_) (_|_|_) (_|_|_),
    tidy,
  end }

variables (L : α → C) (R : β → C) (F : Π b, L (fst b) ⟶ R b) (S : Π b, L (snd b) ⟶ R b)

@[simp]
lemma multipair_obj_zero (a) : (multipair _ _ F S).obj (walking_multipair.zero a) = L a := rfl

@[simp]
lemma multipair_obj_one (a) : (multipair _ _ F S).obj (walking_multipair.one a) = R a := rfl

@[simp]
lemma multipair_map_fst (a) : (multipair _ _ F S).map (walking_multipair.hom.fst a) =
  F a := rfl

@[simp]
lemma multipair_map_snd (a) : (multipair _ _ F S).map (walking_multipair.hom.snd a) =
  S a := rfl

def multifork := cone (multipair _ _ F S)

variables {L R F S}

def multifork.ι (K : multifork _ _ F S) (a : α) : K.X ⟶ L a :=
K.π.app (walking_multipair.zero a)

@[simp]
lemma multifork.ι_eq_app_zero (K : multifork _ _ F S) (a : α) : K.ι a =
  K.π.app (walking_multipair.zero a) := rfl

@[simp]
lemma multifork.app_zero_fst (K : multifork _ _ F S) (b : β) :
  K.π.app (walking_multipair.zero (fst b)) ≫ F b = K.π.app (walking_multipair.one b) :=
by { rw [← K.w (walking_multipair.hom.fst b)], refl }

@[simp]
lemma multifork.app_one_snd (K : multifork _ _ F S) (b : β) :
  K.π.app (walking_multipair.zero (snd b)) ≫ S b = K.π.app (walking_multipair.one b) :=
by { rw [← K.w (walking_multipair.hom.snd b)], refl }

@[simps]
def multifork.of_ι {P : C} (ι : Π a, P ⟶ L a) (w : ∀ b, ι (fst b) ≫ F b = ι (snd b) ≫ S b) :
  multifork _ _ F S :=
{ X := P,
  π :=
  { app := λ x,
    match x with
    | walking_multipair.zero a := ι _
    | walking_multipair.one b := ι (fst b) ≫ F b
    end,
    naturality' := begin
      rintros (_|_) (_|_) (_|_|_),
      any_goals { symmetry, dsimp, rw category.id_comp, apply category.comp_id },
      { dsimp, rw category.id_comp, refl },
      { dsimp, rw category.id_comp, apply w }
    end } }

@[reassoc]
lemma multifork.condition (K : multifork _ _ F S) (b : β) :
  K.ι (fst b) ≫ F b = K.ι (snd b) ≫ S b := by simp

variables (L R F S)

abbreviation has_multiequalizer := has_limit (multipair _ _ F S)

variables [has_multiequalizer L R F S]

noncomputable theory

abbreviation multiequalizer := limit (multipair _ _ F S)

abbreviation multiequalizer.ι (a) : multiequalizer _ _ F S ⟶ L a :=
limit.π _ (walking_multipair.zero _)

abbreviation multiequalizer.multifork : multifork _ _ F S := limit.cone _

@[simp]
lemma multiequalizer.multifork_ι (a) :
  (multiequalizer.multifork _ _ F S).ι a = multiequalizer.ι _ _ F S a := rfl

@[simp]
lemma multiequalizer.multifork_π_app_zero (a) :
  (multiequalizer.multifork _ _ F S).π.app (walking_multipair.zero a) =
  multiequalizer.ι _ _ F S a := rfl

@[reassoc]
lemma multiequalizer.condition (b) :
  multiequalizer.ι _ _ F S (fst b) ≫ F b = multiequalizer.ι _ _ F S (snd b) ≫ S b :=
multifork.condition _ _

abbreviation multiequalizer.lift {W : C} (k : Π a, W ⟶ L a)
  (h : ∀ b, k (fst b) ≫ F b = k (snd b) ≫ S b) :
  W ⟶ multiequalizer _ _ F S :=
limit.lift _ (multifork.of_ι k h)

@[simp, reassoc]
lemma multiequalizer.lift_ι {W : C} (k : Π a, W ⟶ L a)
  (h : ∀ b, k (fst b) ≫ F b = k (snd b) ≫ S b) (a) :
  multiequalizer.lift _ _ F S k h ≫ multiequalizer.ι _ _ F S a = k _ :=
limit.lift_π _ _

@[ext]
lemma multiequalizer.hom_ext {W : C} (i j : W ⟶ multiequalizer _ _ F S)
  (h : ∀ a, i ≫ multiequalizer.ι _ _ F S a = j ≫ multiequalizer.ι _ _ F S a) :
  i = j :=
limit.hom_ext
begin
  rintro (a|b),
  { apply h },
  simp_rw [← limit.w (multipair _ _ F S) (walking_multipair.hom.fst b), ← category.assoc, h],
end

end category_theory.limits
