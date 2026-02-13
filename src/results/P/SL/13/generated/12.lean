

theorem Topology.closed_P3_implies_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X:=X) A) :
    IsOpen (A : Set X) := by
  have h_closure : closure (A : Set X) = A := hA_closed.closure_eq
  have h_subset : (A : Set X) ⊆ interior A := by
    dsimp [Topology.P3] at hP3
    simpa [h_closure] using hP3
  have h_eq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · exact h_subset
  have : IsOpen (interior A) := isOpen_interior
  simpa [h_eq] using this