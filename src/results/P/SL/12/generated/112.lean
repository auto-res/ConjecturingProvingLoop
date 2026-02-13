

theorem Topology.P3_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P3 (X := X) (interior (closure (interior (closure A)))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  simpa using
    Topology.isOpen_P3 (X := X)
      (A := interior (closure (interior (closure A)))) h_open