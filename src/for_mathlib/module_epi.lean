import linear_algebra.quotient
import algebra.category.Module.basic

namespace module

variables {A : Type*} [ring A] {M N L : Type*}
  [add_comm_group M]
  [add_comm_group N]
  [add_comm_group L]
  [module A M]
  [module A N]
  [module A L]
  (f : M →ₗ[A] N)
  (g : M →ₗ[A] L)

def compare_in_prod : M →ₗ[A] N × L :=
{ to_fun := λ m, ⟨f m , - g m⟩,
  map_add' := λ x y, by ext; simp [add_comm],
  map_smul' := λ r x, by ext; simp }

@[derive add_comm_group]
def pushout :=
(N × L) ⧸ (compare_in_prod f g).range

instance : module A (pushout f g) :=
show (module A ((N × L) ⧸ (compare_in_prod f g).range)), by apply_instance

def pushout.π : N × L →ₗ[A] pushout f g :=
(compare_in_prod f g).range.mkq -- mkq?

def pushout.inl : N →ₗ[A] pushout f g :=
{ to_fun := λ n, pushout.π _ _ (n,0),
  map_add' := λ x y, by { rw ← (pushout.π f g).map_add, congr' 1, ext; simp },
  map_smul' := λ r x, by { rw ← (pushout.π f g).map_smul, congr' 1, ext; simp } }

def pushout.inr : L →ₗ[A] pushout f g :=
{ to_fun := λ l, pushout.π _ _ (0,l),
  map_add' := λ x y, by { rw ← (pushout.π f g).map_add, congr' 1, ext; simp },
  map_smul' := λ r x, by { rw ← (pushout.π f g).map_smul, congr' 1, ext; simp } }

lemma surjective_of_comp_inl_eq_comp_inr (f : M →ₗ[A] N)
  (h :
    pushout.inl f.range.subtype f.range.subtype =
    pushout.inr f.range.subtype f.range.subtype ) : function.surjective f :=
begin
  intros b,
  apply_fun (λ e, e b) at h,
  dsimp [pushout.inl, pushout.inr, pushout.π] at h,
  rw submodule.quotient.eq at h,
  simp at h,
  obtain ⟨⟨a,⟨a,rfl⟩⟩,ht⟩ := h,
  dsimp [compare_in_prod] at ht,
  apply_fun (λ e, e.fst) at ht,
  use a,
  exact ht,
end

end module

open category_theory

namespace Module

universes u
theorem surjective_of_epi {A : Type u} [ring A] {M N : Module.{u} A}
  (f : M ⟶ N) [epi f] : function.surjective f :=
begin
  apply module.surjective_of_comp_inl_eq_comp_inr,
  apply_fun Module.of_hom,
  swap, { tidy },
  erw ← cancel_epi f,
  change linear_map.comp _ _ = linear_map.comp _ _,
  ext,
  dsimp [Module.of_hom, module.pushout.inl, module.pushout.inr, module.pushout.π],
  rw submodule.quotient.eq,
  simp,
  use ⟨_,⟨x,rfl⟩⟩,
  refl,
end

end Module
