

theorem Topology.P1_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P1 (X := X) (A := interior (closure (interior A))) hOpen