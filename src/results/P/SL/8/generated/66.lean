

theorem P2_closureInterior_iff_isOpen_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    Topology.closed_P2_iff_isOpen (X := X) (A := closure (interior A)) h_closed