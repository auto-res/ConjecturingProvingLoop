

theorem Topology.P2_closure_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using (Topology.P2_closed_iff_isOpen (A := closure A) hClosed)