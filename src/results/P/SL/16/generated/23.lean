

theorem Topology.P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P2 (X := X) (A := interior (closure A)) hOpen