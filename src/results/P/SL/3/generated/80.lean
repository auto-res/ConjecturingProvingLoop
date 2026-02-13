

theorem P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (A := closure (A : Set X)) hClosed)