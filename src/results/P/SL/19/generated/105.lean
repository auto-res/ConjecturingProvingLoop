

theorem Topology.P2_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (A := interior (closure (interior (closure A)))) := by
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  exact Topology.P2_of_isOpen
      (A := interior (closure (interior (closure A)))) hOpen