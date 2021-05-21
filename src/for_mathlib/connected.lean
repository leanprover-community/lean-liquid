import topology.connected

instance prod.totally_disconnected_space (X Y : Type*)
  [topological_space X] [topological_space Y]
  [totally_disconnected_space X] [totally_disconnected_space Y] :
  totally_disconnected_space (X × Y) :=
⟨λ t h1 h2,
have H1 : is_preconnected (prod.fst '' t), from h2.image prod.fst continuous_fst.continuous_on,
have H2 : is_preconnected (prod.snd '' t), from h2.image prod.snd continuous_snd.continuous_on,
λ x hx y hy, prod.ext
  (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
  (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩
