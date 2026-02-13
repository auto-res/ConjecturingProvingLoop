

theorem Topology.P2_closure_iff_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P2_iff_isOpen_of_isClosed (A := closure A) hClosed)