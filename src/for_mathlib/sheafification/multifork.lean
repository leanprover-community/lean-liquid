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

structure multipair.index (fst snd : β → α) (C : Type u) [category.{v} C] :=
(L : α → C)
(R : β → C)
(F : Π b, L (fst b) ⟶ R b)
(S : Π b, L (snd b) ⟶ R b)

variable (I : multipair.index fst snd C)

def multipair : walking_multipair fst snd ⥤ C :=
{ obj := λ x,
  match x with
  | walking_multipair.zero a := I.L a
  | walking_multipair.one b := I.R b
  end,
  map := λ x y f,
  match x, y, f with
  | _, _, walking_multipair.hom.id x := 𝟙 _
  | _, _, walking_multipair.hom.fst b := I.F _
  | _, _, walking_multipair.hom.snd b := I.S _
  end,
  map_id' := begin
    rintros (_|_),
    tidy,
  end,
  map_comp' := begin
    rintros (_|_) (_|_) (_|_) (_|_|_) (_|_|_),
    tidy,
  end }

--variables (L : α → C) (R : β → C) (F : Π b, L (fst b) ⟶ R b) (S : Π b, L (snd b) ⟶ R b)

@[simp]
lemma multipair_obj_zero (a) : (multipair I).obj (walking_multipair.zero a) = I.L a := rfl

@[simp]
lemma multipair_obj_one (a) : (multipair I).obj (walking_multipair.one a) = I.R a := rfl

@[simp]
lemma multipair_map_fst (a) : (multipair I).map (walking_multipair.hom.fst a) =
  I.F a := rfl

@[simp]
lemma multipair_map_snd (a) : (multipair I).map (walking_multipair.hom.snd a) =
  I.S a := rfl

--variables (fst snd)

def multifork := cone (multipair I)

--variables {fst snd}

--variables {L R F S}
variable {I}

def multifork.ι (K : multifork I) (a : α) : K.X ⟶ I.L a :=
K.π.app (walking_multipair.zero a)

@[simp]
lemma multifork.ι_eq_app_zero (K : multifork I) (a : α) : K.ι a =
  K.π.app (walking_multipair.zero a) := rfl

@[simp]
lemma multifork.app_zero_fst (K : multifork I) (b : β) :
  K.π.app (walking_multipair.zero (fst b)) ≫ I.F b = K.π.app (walking_multipair.one b) :=
by { rw [← K.w (walking_multipair.hom.fst b)], refl }

@[simp]
lemma multifork.app_one_snd (K : multifork I) (b : β) :
  K.π.app (walking_multipair.zero (snd b)) ≫ I.S b = K.π.app (walking_multipair.one b) :=
by { rw [← K.w (walking_multipair.hom.snd b)], refl }

--variables (fst snd L R F S)
variable (I)
@[simps]
def multifork.of_ι (P : C) (ι : Π a, P ⟶ I.L a) (w : ∀ b, ι (fst b) ≫ I.F b = ι (snd b) ≫ I.S b) :
  multifork I :=
{ X := P,
  π :=
  { app := λ x,
    match x with
    | walking_multipair.zero a := ι _
    | walking_multipair.one b := ι (fst b) ≫ I.F b
    end,
    naturality' := begin
      rintros (_|_) (_|_) (_|_|_),
      any_goals { symmetry, dsimp, rw category.id_comp, apply category.comp_id },
      { dsimp, rw category.id_comp, refl },
      { dsimp, rw category.id_comp, apply w }
    end } }
--variables {fst snd L R F S}

variable {I}

@[reassoc]
lemma multifork.condition (K : multifork I) (b : β) :
  K.ι (fst b) ≫ I.F b = K.ι (snd b) ≫ I.S b := by simp

--variables (fst snd L R F S)

variable (I)

abbreviation has_multiequalizer := has_limit (multipair I)

variables [has_multiequalizer I]

noncomputable theory

abbreviation multiequalizer := limit (multipair I)

abbreviation multiequalizer.ι (a) : multiequalizer I ⟶ I.L a :=
limit.π _ (walking_multipair.zero _)

abbreviation multiequalizer.multifork : multifork I := limit.cone _

@[simp]
lemma multiequalizer.multifork_ι (a) :
  (multiequalizer.multifork I).ι a = multiequalizer.ι I a := rfl

@[simp]
lemma multiequalizer.multifork_π_app_zero (a) :
  (multiequalizer.multifork I).π.app (walking_multipair.zero a) =
  multiequalizer.ι I a := rfl

@[reassoc]
lemma multiequalizer.condition (b) :
  multiequalizer.ι I (fst b) ≫ I.F b =
  multiequalizer.ι I (snd b) ≫ I.S b :=
multifork.condition _ _

abbreviation multiequalizer.lift {W : C} (k : Π a, W ⟶ I.L a)
  (h : ∀ b, k (fst b) ≫ I.F b = k (snd b) ≫ I.S b) :
  W ⟶ multiequalizer I :=
limit.lift _ (multifork.of_ι I _ k h)

@[simp, reassoc]
lemma multiequalizer.lift_ι {W : C} (k : Π a, W ⟶ I.L a)
  (h : ∀ b, k (fst b) ≫ I.F b = k (snd b) ≫ I.S b) (a) :
  multiequalizer.lift I k h ≫ multiequalizer.ι I a = k _ :=
limit.lift_π _ _

@[ext]
lemma multiequalizer.hom_ext {W : C} (i j : W ⟶ multiequalizer I)
  (h : ∀ a, i ≫ multiequalizer.ι I a =
  j ≫ multiequalizer.ι I a) :
  i = j :=
limit.hom_ext
begin
  rintro (a|b),
  { apply h },
  simp_rw [← limit.w (multipair I) (walking_multipair.hom.fst b), ← category.assoc, h],
end

end category_theory.limits
