

theorem P2_closure_interior_closure_iff_isOpen_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure (A : Set X)))) ↔
      IsOpen (closure (interior (closure (A : Set X)))) := by
  have hClosed : IsClosed (closure (interior (closure (A : Set X)))) :=
    isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X)
      (A := closure (interior (closure (A : Set X))))
      hClosed)