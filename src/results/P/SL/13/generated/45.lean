

theorem Topology.P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have h_closed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := closure A) h_closed)