

theorem interior_prod_nonempty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (interior A).Nonempty → (interior B).Nonempty → (interior (A ×ˢ B)).Nonempty := by
  intro hA hB
  rcases hA with ⟨x, hx⟩
  rcases hB with ⟨y, hy⟩
  have : ((x, y) : X × Y) ∈ interior (A ×ˢ B) := by
    -- Rewrite the target interior using `interior_prod_eq`.
    have hMem : ((x, y) : X × Y) ∈ interior A ×ˢ interior B := ⟨hx, hy⟩
    simpa [interior_prod_eq] using hMem
  exact ⟨(x, y), this⟩