

theorem P3_closure_interior_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P3_iff_open_of_closed (A := closure (interior A)) hClosed)