

theorem Set.inter_distrib_left {α : Type*} {s t u : Set α} :
    s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx_s, hxtu⟩
    cases hxtu with
    | inl hx_t => exact Or.inl ⟨hx_s, hx_t⟩
    | inr hx_u => exact Or.inr ⟨hx_s, hx_u⟩
  · intro hx
    cases hx with
    | inl hst => exact ⟨hst.1, Or.inl hst.2⟩
    | inr hsu => exact ⟨hsu.1, Or.inr hsu.2⟩