

theorem Topology.P3_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior (closure (interior A))) hOpen