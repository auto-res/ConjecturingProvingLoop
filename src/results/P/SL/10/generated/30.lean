

theorem Topology.P1_iff_closure_interior_eq_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hClosed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_of_P1_and_isClosed (X := X) (A := A) hP1 hClosed
  · intro h_eq
    dsimp [Topology.P1]
    intro x hx
    simpa [h_eq] using hx