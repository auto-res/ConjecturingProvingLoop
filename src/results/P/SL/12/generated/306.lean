

theorem Topology.isClosed_interior_iff_closure_interior_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed (interior (A : Set X)) ↔ closure (interior A) = interior A := by
  constructor
  · intro h_closed
    simpa using h_closed.closure_eq
  · intro h_eq
    have h_subset : closure (interior (A : Set X)) ⊆ interior A := by
      simpa [h_eq]
    exact isClosed_of_closure_subset h_subset