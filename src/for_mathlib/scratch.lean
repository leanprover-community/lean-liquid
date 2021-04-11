
/-
def cofinal_system (X : Profinite.{u}) : Type u :=
Π (I : X.clopen_cover), Σ (J : X.clopen_cover) (h : plift (J ≤ I)), J

namespace cofinal_system

variable {X : Profinite}

def lift (Us : X.cofinal_system) (U : X.clopen_cover) : X.clopen_cover := (Us U).1

def lift_le (Us : X.cofinal_system) (U : X.clopen_cover) : Us.lift U ≤ U := (Us U).2.1.down

def point (Us : X.cofinal_system) (U : X.clopen_cover) : Us.lift U := (Us U).2.2

open clopen_cover

structure compat (Us : X.cofinal_system) (I J : X.clopen_cover) : Prop :=
(compat_left :
  map (inf_le_left : _ ≤ Us.lift I) (map (Us.lift_le (Us.lift I ⊓ Us.lift J)) (Us.point _)) =
  Us.point _)
(compat_right :
  map (inf_le_right : _ ≤ Us.lift J) (map (Us.lift_le (Us.lift I ⊓ Us.lift J)) (Us.point _)) =
  Us.point _)

end cofinal_system

namespace clopen_cover

variable {X : Profinite}

section proj

lemma eq_of_proj_eq_cofinal {x y : X} (Us : X.cofinal_system) :
  (∀ I : X.clopen_cover, (Us.lift I).proj x = (Us.lift I).proj y) → x = y :=
begin
  intros h,
  apply eq_of_forall_proj_eq,
  intros I,
  specialize h I,
  have hx : I.proj x = map (Us.lift_le I) ((Us.lift I).proj x), by simp [proj_map_comm],
  have hy : I.proj y = map (Us.lift_le I) ((Us.lift I).proj y), by simp [proj_map_comm],
  rw [hx, hy, h],
end

lemma exists_of_compat_cofinal (Us : X.cofinal_system)
  (compat : ∀ I J, Us.compat I J) : ∃ x : X, ∀ I, (Us.lift I).proj x = Us.point I :=
begin
  let Vs : Π (I : X.clopen_cover), I := λ I, map (Us.lift_le I) (Us.point _),
  swap,
  rcases exists_of_compat Vs _ with ⟨x,hx⟩,
  refine ⟨x,_⟩,
  { intros I,
    dsimp [Vs] at hx,
    rw hx,
    rw [← (compat (Us.lift I) I).compat_left, ← (compat (Us.lift I) I).compat_right],
    simp_rw [← map_comp],
    refl },
  { intros I J h,
    dsimp [Vs],
    rw [← (compat I J).compat_left, ← (compat I J).compat_right],
    simp_rw [← map_comp],
    refl }
end

def π (I : X.clopen_cover) : X ⟶ of_Fintype.obj (Fintype.of I) :=
{ to_fun := proj _,
  continuous_to_fun := locally_constant.continuous _ }

end proj

end clopen_cover

-/


/-
namespace limit_rep

open clopen_cover

variables {J : Type u} [small_category J] (F : J ⥤ Profinite.{u})

structure index_cat : Type u :=
(I : Π j : J, (F.obj j).clopen_cover)
(le : Π {i j : J} (f : i ⟶ j), le_rel (F.map f) (I i) (I j))

namespace index_cat

variable {F}

structure hom (A B : index_cat F) : Type u :=
(le : ∀ j : J, A.I j ≤ B.I j)

instance : small_category (index_cat F) :=
{ hom := hom,
  id := λ X, ⟨λ j, le_refl _⟩,
  comp := λ X Y Z f g, ⟨λ j, le_trans (f.le j) (g.le j)⟩,
  id_comp' := λ X Y f, by {cases f, refl},
  comp_id' := λ X Y f, by {cases f, refl},
  assoc' := λ X Y Z W f g h, by {cases f, cases g, cases h, refl} }

end index_cat

@[simps]
def diagram : index_cat F ⥤ J ⥤ Fintype.{u} :=
{ obj := λ II,
  { obj := λ j, Fintype.of $ II.I j,
    map := λ i j f, clopen_cover.map (II.le f),
    map_id' := λ j, begin
      ext1 x,
      simp,
    end,
    map_comp' := λ i j k f g, begin
      ext1 x,
      simp,
      rw ← map_comp,
    end },
  map := λ II JJ f,
  { app := λ j, map (f.le j),
    naturality' := begin
      intros i j g,
      ext1,
      dsimp,
      simp_rw ← map_comp,
      refl,
    end },
  map_id' := begin
    intros II,
    ext1,
    ext1 j,
    ext1 x,
    dsimp at *,
    erw map_id,
  end,
  map_comp' := begin
    intros II JJ KK f g,
    ext1,
    ext1 j,
    ext1 x,
    dsimp at *,
    rw ← map_comp,
    refl,
  end }.

abbreviation diagram' : index_cat F ⥤ J ⥤ Profinite :=
  diagram F ⋙ (whiskering_right _ _ _).obj of_Fintype

def mk_cofinal (j : J)
  (cond : ∀ I : (F.obj j).clopen_cover, ∃ (II : index_cat F), II.I j ≤ I) :
  cofinal_system (F.obj j) := λ I,
{ fst := (classical.some (cond I)).I j,
  snd :=
  { fst := plift.up (classical.some_spec (cond I)),
    snd := _ } }

def Fincone : limits.cone (diagram' F) :=
{ X := F,
  π :=
  { app := λ II,
    { app := λ j, π _,
      naturality' := begin
        intros i j f,
        ext1 x,
        dsimp [π, diagram, of_Fintype],
        rw proj_map_comm,
      end },
    naturality' := begin
      intros II JJ f,
      ext1,
      ext1 j,
      ext1 x,
      dsimp [π, diagram, of_Fintype],
      rw proj_map_comm,
      refl,
    end } }.

def limit_cone : limits.limit_cone (diagram' F) :=
{ cone := limits.combine_cones _ (λ j, limit_cone _),
  is_limit := limits.combined_is_limit _ _ }

def is_iso_lift {j : J} (cond : ∀ I : (F.obj j).clopen_cover, ∃ (II : index_cat F), II.I j ≤ I) :
  is_iso (((limit_cone F).is_limit.lift (Fincone F)).app j) :=
begin
  apply is_iso_of_bijective,
  split,
  { intros x y h,
    let Us : cofinal_system (F.obj j) := λ I,
      ⟨(classical.some (cond I)).I j,plift.up (classical.some_spec (cond I)),proj _ x⟩,
    apply eq_of_proj_eq_cofinal Us,
    intros I,
    dsimp [cofinal_system.lift],
    let II : index_cat F := classical.some (cond I),
    apply_fun subtype.val at h,
    apply_fun (λ g, g II) at h,
    exact h },
  { intros x,
    let Us : cofinal_system (F.obj j) := λ I,
      ⟨( classical.some (cond I)).I j,
         plift.up (classical.some_spec (cond I)),
         x.val (classical.some (cond I))⟩,
    have := exists_of_compat_cofinal Us _,
    rcases this with ⟨a,ha⟩,
    refine ⟨a,_⟩,
    ext1,
    ext1 II,
    specialize ha (II.I j),
    change proj _ a = _,
    cases x with x hx,
    dsimp at *,
    -- I dont think this works.
    sorry,
  }
end

--lemma lift_is_iso : is_iso ((limit_cone F).is_limit.lift (Fincone F)) :=
--nat_iso.is_iso_of_is_iso_app _

end limit_rep
-/
