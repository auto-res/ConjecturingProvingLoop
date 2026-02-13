

theorem P3_closure_iff_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P3_closed_iff_open hClosed)