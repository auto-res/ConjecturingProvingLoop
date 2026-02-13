

theorem P3_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    have h_closure : closure A = A := hA_closed.closure_eq
    have h_subset : A ⊆ interior A := by
      simpa [Topology.P3, h_closure] using hP3
    have h_eq : interior A = A := Set.Subset.antisymm interior_subset h_subset
    have h_open_int : IsOpen (interior A) := isOpen_interior
    simpa [h_eq] using h_open_int
  · intro hA_open
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hA_open