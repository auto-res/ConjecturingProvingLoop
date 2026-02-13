

theorem interior_nonempty_iff_nonempty_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → ((interior A).Nonempty ↔ A.Nonempty) := by
  intro hP2
  constructor
  · intro hInt
    rcases hInt with ⟨x, hx⟩
    exact ⟨x, interior_subset hx⟩
  · intro hA
    exact
      Topology.interior_nonempty_of_P2 (X := X) (A := A) hP2 hA