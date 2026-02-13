

theorem Topology.P3_closureInterior_iff_isOpen_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := closure (interior A)) h_closed)