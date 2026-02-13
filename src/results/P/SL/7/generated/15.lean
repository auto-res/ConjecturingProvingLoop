

theorem Topology.P3_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    -- From P3 and closedness we deduce openness.
    have hsub : (A : Set X) ⊆ interior A := by
      simpa [Topology.P3, hA.closure_eq] using hP3
    have hEq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hsub
    have : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using this
  · intro hOpen
    exact (IsOpen_P1_and_P3 (A := A) hOpen).2