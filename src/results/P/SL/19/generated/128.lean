

theorem Topology.P3_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P3_of_isOpen (A := interior (closure (interior A))) hOpen