

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    have h_subset : A ⊆ interior A := by
      have : A ⊆ interior (closure A) := hP3
      simpa [hClosed.closure_eq] using this
    have h_eq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact h_subset
    have h_open : IsOpen (interior A) := isOpen_interior
    simpa [h_eq] using h_open
  · intro hOpen
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen