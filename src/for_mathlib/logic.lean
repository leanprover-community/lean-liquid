import logic.nonempty

instance {α : Type*} {β : α → Type*} [Π a, nonempty (β a)] : nonempty (Π a, β a) :=
⟨λ _, classical.arbitrary _⟩
