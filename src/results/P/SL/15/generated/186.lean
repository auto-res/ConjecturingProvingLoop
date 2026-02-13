

theorem P2_closure_interior_closure_iff_isOpen_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  simpa using
    (Topology.P2_closure_interior_iff_isOpen_closure_interior
      (X := X) (A := closure A))