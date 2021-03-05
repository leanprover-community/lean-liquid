import category_theory.limits.shapes.zero

open category_theory category_theory.limits

class has_succ (α : Type*) := (succ : α → α)

-- fix this to something better?
notation `Ş` := has_succ.succ

-- do we want this for every semiring??
instance : has_succ ℕ := ⟨λ n, n + 1⟩
instance : has_succ ℤ := ⟨λ n, n + 1⟩

structure differential_object_aux (ι : Type) (S₀ S₁ : ι → ι) (V : Type*)
  [category V] [has_zero_morphisms V] :=
(X : ι → V)
(differential : Π i, X (S₀ i) ⟶ X (S₁ i))
(differential2 : ∀ i j (h : S₁ i = S₀ j),
  differential i ≫ eq_to_hom (show X (S₁ i) = X (S₀ j), by rw h) ≫ differential j = 0)

variables (ι : Type) (V : Type*) {cov : bool}
variables [has_succ ι] [category V] [has_zero_morphisms V]

def differential_object : bool → Type*
| tt := differential_object_aux ι id Ş V
| ff := differential_object_aux ι Ş id V

abbreviation chain_complex := differential_object ι V ff

abbreviation cochain_complex := differential_object ι V tt

namespace differential_object

variables {ι V}

def X : Π {cov : bool} (C : differential_object ι V cov), ι → V
| tt := differential_object_aux.X
| ff := differential_object_aux.X

variable [decidable_eq ι]

def coherent_indices : Π (cov : bool) (i j : ι), Prop
| tt i j := Ş i = j
| ff i j := i = Ş j

def d : Π {cov : bool} (C : differential_object ι V cov) (i j : ι), C.X i ⟶ C.X j
| tt C i j :=
if h : Ş i = j
then differential_object_aux.differential C i ≫ eq_to_hom (show C.X (Ş i) = C.X j, by rw h)
else 0
| ff C i j :=
if h : i = Ş j
then eq_to_hom (show C.X i = C.X (Ş j), by rw h) ≫ differential_object_aux.differential C j
else 0

variables (C C₁ C₂ C₃ : differential_object ι V cov)

lemma d_eq_zero (i j : ι) (h : ¬ coherent_indices cov i j) : C.d i j = 0 :=
by { cases cov; dsimp [d, coherent_indices] at h ⊢; simp only [dif_neg h] }

lemma d_comp_d (i j k : ι) : C.d i j ≫ C.d j k = 0 :=
begin
  cases cov,
  all_goals
  { dsimp [d], split_ifs with h1 h2,
    { subst h1, subst h2,
      simpa using differential_object_aux.differential2 C _ _ rfl },
    all_goals { simp only [zero_comp, comp_zero] } }
end

@[ext]
structure hom :=
(f (i : ι) : C₁.X i ⟶ C₂.X i)
(comm' (i j : ι) (h : coherent_indices cov i j) : C₁.d i j ≫ f j = f i ≫ C₂.d i j)

variables {C₁ C₂ C₃}

@[reassoc]
lemma hom.comm (f : hom C₁ C₂) (i j : ι) :
  C₁.d i j ≫ f.f j = f.f i ≫ C₂.d i j :=
begin
  by_cases h : coherent_indices cov i j,
  { exact f.comm' i j h },
  simp only [d_eq_zero _ i j h, zero_comp, comp_zero]
end

def id : hom C C :=
{ f := λ i, 𝟙 _,
  comm' := by { intros, simp only [category.id_comp, category.comp_id] } }

def comp (f : hom C₁ C₂) (g : hom C₂ C₃) : hom C₁ C₃ :=
{ f := λ i, f.f i ≫ g.f i,
  comm' := λ i j hij, by { rw [hom.comm_assoc, hom.comm, category.assoc] } }

instance : category (differential_object ι V cov) :=
{ hom := hom,
  id := id,
  comp := λ _ _ _, comp,
  id_comp' := by { intros, ext, dsimp [id, comp], rw [category.id_comp] },
  comp_id' := by { intros, ext, dsimp [id, comp], rw [category.comp_id] },
  assoc' := by { intros, ext, dsimp [id, comp], rw [category.assoc] } }

@[simp] lemma id_f (i : ι) : (𝟙 C : C ⟶ C).f i = 𝟙 (C.X i) := rfl

@[simp] lemma comp_f (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  (f ≫ g).f i = f.f i ≫ g.f i := rfl

def iso_app (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
{ hom := f.hom.f i,
  inv := f.inv.f i,
  hom_inv_id' := by { rw [← comp_f, f.hom_inv_id, id_f] },
  inv_hom_id' := by { rw [← comp_f, f.inv_hom_id, id_f] } }

end differential_object
