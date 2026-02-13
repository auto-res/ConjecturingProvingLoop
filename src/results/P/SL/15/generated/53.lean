

theorem P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  constructor
  · intro hP3
    have h_subset : A ⊆ interior A := by
      dsimp [Topology.P3] at hP3
      simpa [hA_closed.closure_eq] using hP3
    exact Set.Subset.antisymm interior_subset h_subset
  · intro hIntEq
    have hOpen : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [hIntEq] using this
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen