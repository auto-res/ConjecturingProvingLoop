

theorem interior_P3 {X : Type*} [TopologicalSpace X] (A : Set X) :
    P3 (interior A) := by
  dsimp [P3]
  intro x hx
  have hx' : x ∈ interior (interior A) := by
    simpa [isOpen_interior.interior_eq] using hx
  have hsubset : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono (subset_closure : interior A ⊆ closure (interior A))
  exact hsubset hx'