

theorem Topology.isOpen_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (interior (closure (interior A))) := by
  exact isOpen_interior