

theorem Topology.P1_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := interior (closure (interior A))) := by
  exact Topology.P1_of_isOpen
    (A := interior (closure (interior A))) isOpen_interior