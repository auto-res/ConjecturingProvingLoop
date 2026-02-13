

theorem P1_interior_closure_iff_P2_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P1 (interior (closure (A : Set X))) ↔
      Topology.P2 (interior (closure (A : Set X))) := by
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa using
    (Topology.P1_iff_P2_of_isOpen
      (A := interior (closure (A : Set X)))
      hOpen)