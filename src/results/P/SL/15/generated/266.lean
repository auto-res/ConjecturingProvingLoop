

theorem interior_nonempty_iff_nonempty_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → ((interior A).Nonempty ↔ A.Nonempty) := by
  intro hP1
  constructor
  · intro hInt
    rcases hInt with ⟨x, hx⟩
    exact ⟨x, interior_subset hx⟩
  · intro hA
    exact
      Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA