

theorem Topology.P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.P3_of_isOpen (A := interior (closure A)) hOpen