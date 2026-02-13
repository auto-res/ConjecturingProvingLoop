

theorem Topology.P3_closure_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using (Topology.P3_closed_iff_isOpen (A := closure A) hClosed)