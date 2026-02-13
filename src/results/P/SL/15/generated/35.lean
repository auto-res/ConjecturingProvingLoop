

theorem P2_closure_interior_iff_isOpen_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P2_closed_iff_isOpen (X := X) (A := closure (interior A)) h_closed)