

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  -- `P2 A → P3 A` holds without any extra assumptions
  have h₁ : P2 A → P3 A := fun h => P2_to_P3 h
  -- Prove `P3 A → P2 A` assuming `A` is closed
  have h₂ : P3 A → P2 A := by
    intro hP3
    intro x hxA
    -- From `hP3` we obtain that `x ∈ interior A`
    have hx_intA : x ∈ interior A := by
      have hx : x ∈ interior (closure A) := hP3 hxA
      simpa [hA.closure_eq] using hx
    -- Show that `interior A ⊆ interior (closure (interior A))`
    have h_subset : interior A ⊆ interior (closure (interior A)) := by
      have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      simpa [interior_interior] using h'
    exact h_subset hx_intA
  exact ⟨h₁, h₂⟩