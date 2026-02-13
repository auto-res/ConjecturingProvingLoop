

theorem Topology.P2_closure_interior_iff_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.closed_P2_iff_isOpen (X := X) (A := closure (interior A)) hClosed)